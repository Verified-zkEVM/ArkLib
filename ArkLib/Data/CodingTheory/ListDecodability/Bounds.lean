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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
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

open scoped ProbabilityTheory in
theorem Pr_add_compl {α : Type} (p : PMF α) (P : α → Prop)
    [DecidablePred P] :
    Pr_{ let a ← p }[P a] + Pr_{ let a ← p }[¬P a] = 1 := by
  rw [ProbabilityTheory.Pr_eq_tsum_indicator,
    ProbabilityTheory.Pr_eq_tsum_indicator]
  rw [← ENNReal.tsum_add]
  have hfun :
      (fun a => p a * (if P a then (1 : ENNReal) else 0) +
        p a * (if ¬P a then (1 : ENNReal) else 0)) = p := by
    funext a
    by_cases h : P a <;>
      simp only [h, if_true, if_false, not_true_eq_false,
        not_false_eq_true, mul_one, mul_zero, add_zero, zero_add]
  rw [hfun, PMF.tsum_coe]

open scoped ProbabilityTheory in
theorem Pr_uniform_eq_card_subtype_div {α : Type} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] :
    Pr_{ let a ← $ᵖ α }[P a] =
      (Fintype.card {a : α // P a} : ENNReal) / Fintype.card α := by
  rw [ProbabilityTheory.Pr_eq_tsum_indicator]
  simp only [PMF.uniformOfFintype_apply, tsum_fintype]
  change (∑ a : α, (Fintype.card α : ENNReal)⁻¹ * if P a then 1 else 0) =
    (Fintype.card {a : α // P a} : ENNReal) *
      (Fintype.card α : ENNReal)⁻¹
  rw [mul_comm (Fintype.card {a : α // P a} : ENNReal), ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_boole]
  norm_cast
  exact (Fintype.card_subtype P).symm

open scoped ProbabilityTheory in
theorem Pr_uniform_ge_of_card_bound {α : Type} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] (p : ENNReal)
    (hcount : p * (Fintype.card α : ENNReal) ≤
      (Fintype.card {a : α // P a} : ENNReal)) :
    p ≤ Pr_{ let a ← $ᵖ α }[P a] := by
  rw [Pr_uniform_eq_card_subtype_div P]
  have hcard_zero : (Fintype.card α : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard_top : (Fintype.card α : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  exact (ENNReal.le_div_iff_mul_le (Or.inl hcard_zero) (Or.inl hcard_top)).2 hcount

abbrev RSAgreementPattern (t n : ℕ) : Type :=
  Fin n → Finset (Fin t)

structure RSOrientation {t n : ℕ} (H : RSAgreementPattern t n) where
  head : ∀ i : Fin n, (H i).Nonempty → Fin t
  head_mem : ∀ (i : Fin n) (hi : (H i).Nonempty), head i hi ∈ H i

structure RSDirectedPath {t n : ℕ} (H : RSAgreementPattern t n)
    (O : RSOrientation H) (start finish : Fin t) where
  length : ℕ
  edge : Fin length → Fin n
  vertex : Fin (length + 1) → Fin t
  start_eq : vertex ⟨0, Nat.succ_pos length⟩ = start
  finish_eq : vertex (Fin.last length) = finish
  edge_nonempty : ∀ s, (H (edge s)).Nonempty
  tail_mem : ∀ s, vertex (Fin.castSucc s) ∈ H (edge s)
  head_eq : ∀ s, vertex s.succ = O.head (edge s) (edge_nonempty s)

abbrev RSRIMCol {t : ℕ} (root : Fin t) (k : ℕ) :=
  {j : Fin t // j ≠ root} × Fin k

abbrev RSRIMRow {t n : ℕ} (H : RSAgreementPattern t n) :=
  {r : (Σ _ : Fin n, Fin t × Fin t) //
    r.2.1 ∈ H r.1 ∧ r.2.2 ∈ H r.1 ∧ r.2.1 < r.2.2 ∧
      ∀ u ∈ H r.1, r.2.1 ≤ u}

theorem agreement_lower_of_normalized_distance_le
    (n d : ℕ) (r : ℝ) (hn : 0 < n)
    (hd : (d : ℝ) / (n : ℝ) ≤ r) :
    (n : ℝ) * (1 - r) ≤ (n : ℝ) - (d : ℝ) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul : (d : ℝ) ≤ r * (n : ℝ) :=
    (div_le_iff₀ hnreal).mp hd
  nlinarith

theorem card_RSAgreementPattern (t n : ℕ) :
    Fintype.card (RSAgreementPattern t n) = 2 ^ (t * n) := by
  simp only [RSAgreementPattern, Fintype.card_fun, Fintype.card_finset,
    Fintype.card_fin]
  exact (pow_mul 2 t n).symm

theorem card_agreement_eq_card_sub_hammingDist
    {ι A : Type} [Fintype ι] [DecidableEq A] (u v : ι → A) :
    (Finset.univ.filter fun i => u i = v i).card =
      Fintype.card ι - hammingDist u v := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun i => u i = v i)
  have hfilter :
      (Finset.univ.filter fun i : ι => ¬u i = v i) =
        Finset.univ.filter fun i : ι => u i ≠ v i := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter] at h
  unfold hammingDist
  simp only [Finset.card_univ] at h ⊢
  omega

theorem hammingDist_precomp_equiv
    {ι κ A : Type} [Fintype ι] [Fintype κ] [DecidableEq A]
    (e : ι ≃ κ) (u v : κ → A) :
    hammingDist (u ∘ e) (v ∘ e) = hammingDist u v := by
  classical
  unfold hammingDist
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    (e.subtypeEquiv fun i => by rfl)

noncomputable def rsCertificateLength (η : ℝ) (n : ℕ) : ℕ :=
  ⌊η * (n : ℝ) / 2⌋₊

def rsDirectedPathEdges {t n : ℕ} {H : RSAgreementPattern t n}
    {O : RSOrientation H} {start finish : Fin t}
    (P : RSDirectedPath H O start finish) : Finset (Fin n) :=
  Finset.univ.image P.edge

def rsEmbeddingImage {F : Type} [DecidableEq F] (n : ℕ) (α : Fin n ↪ F) :
    {S : Finset F // S.card = n} :=
  ⟨Finset.univ.map α, by simp⟩

noncomputable def rsEmbeddingImageEquiv {F : Type} [DecidableEq F]
    (n : ℕ) (α : Fin n ↪ F) :
    Fin n ≃ ↥(rsEmbeddingImage n α : Finset F) :=
  Equiv.ofBijective
    (fun i : Fin n =>
      (⟨α i, by
        change α i ∈ Finset.univ.map α
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩ :
        ↥(rsEmbeddingImage n α : Finset F)))
    ⟨by
      intro a b hab
      apply α.injective
      exact congrArg Subtype.val hab,
     by
      intro x
      rcases x with ⟨x, hx⟩
      change x ∈ Finset.univ.map α at hx
      obtain ⟨i, _hi, hix⟩ := Finset.mem_map.mp hx
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hix⟩

@[simp] theorem rsEmbeddingImageEquiv_apply {F : Type} [DecidableEq F]
    (n : ℕ) (α : Fin n ↪ F) (i : Fin n) :
    ((rsEmbeddingImageEquiv n α i :
      ↥(rsEmbeddingImage n α : Finset F)) : F) = α i := by
  rfl

theorem rsFinpartition_part_ssubset_of_one_lt_card_parts
    {α : Type} [DecidableEq α] {J : Finset α} (P : Finpartition J)
    (hparts : 1 < P.parts.card) {A : Finset α} (hA : A ∈ P.parts) :
    A ⊂ J := by
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨P.le hA, ?_⟩
  intro hAJ
  obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp hparts
  obtain ⟨D, hD, hDA⟩ : ∃ D ∈ P.parts, D ≠ A := by
    by_cases hBA : B = A
    · exact ⟨C, hC, fun hCA => hBC (hBA.trans hCA.symm)⟩
    · exact ⟨B, hB, hBA⟩
  obtain ⟨x, hxD⟩ := P.nonempty_of_mem_parts hD
  have hxJ : x ∈ J := P.le hD hxD
  have hxA : x ∈ A := by
    rw [hAJ]
    exact hxJ
  have hAD := (P.existsUnique_mem hxJ).unique ⟨hA, hxA⟩ ⟨hD, hxD⟩
  exact hDA hAD.symm

theorem rsFinpartition_parts_nonempty_of_fin_pos
    {t : ℕ} (ht : 0 < t)
    (P : Finpartition (Finset.univ : Finset (Fin t))) :
    P.parts.Nonempty := by
  have huniv : (Finset.univ : Finset (Fin t)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr
      (Fintype.card_pos_iff.mp (by
        simpa only [Fintype.card_fin] using ht))
  exact Finset.nonempty_iff_ne_empty.mpr (by
    intro hparts
    have hempty := P.parts_eq_empty_iff.mp hparts
    rw [hempty] at huniv
    exact Finset.not_nonempty_empty huniv)

open scoped BigOperators in
theorem rsFinpartition_sum_card_sub_one {α : Type} [DecidableEq α]
    {J : Finset α} (P : Finpartition J) :
    ∑ A ∈ P.parts, (((A.card : ℕ) : ℝ) - 1) =
      (J.card : ℝ) - (P.parts.card : ℝ) := by
  have hsumReal :
      (∑ A ∈ P.parts, (A.card : ℝ)) = (J.card : ℝ) := by
    exact_mod_cast P.sum_card_parts
  rw [Finset.sum_sub_distrib, hsumReal]
  simp

theorem rsFinpartition_touched_singleton_card
    {α : Type} [DecidableEq α] {J : Finset α}
    (P : Finpartition J) (x : α) (hx : x ∈ J) :
    (P.parts.filter fun A => (A ∩ {x}).Nonempty).card = 1 := by
  classical
  obtain ⟨A, hA, huniq⟩ := P.existsUnique_mem hx
  rw [Finset.card_eq_one]
  refine ⟨A, ?_⟩
  ext B
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro hB
    obtain ⟨y, hy⟩ := hB.2
    have hy' := Finset.mem_inter.mp hy
    have hyx : y = x := Finset.mem_singleton.mp hy'.2
    apply huniq B
    refine ⟨hB.1, ?_⟩
    rw [← hyx]
    exact hy'.1
  · intro hBA
    subst B
    refine ⟨hA.1, ⟨x, Finset.mem_inter.mpr ⟨hA.2, ?_⟩⟩⟩
    exact Finset.mem_singleton_self x

def rsFinsetCrossing {t : ℕ} (U V : Finset (Fin t)) : Prop :=
  (U ∩ V).Nonempty ∧ (U \ V).Nonempty ∧ (V \ U).Nonempty ∧
    ((Finset.univ : Finset (Fin t)) \ (U ∪ V)).Nonempty

def rsCrossingSupermodular {t : ℕ}
    (p : Finset (Fin t) → ℕ) : Prop :=
  ∀ U V, rsFinsetCrossing U V →
    p U + p V ≤ p (U ∩ V) + p (U ∪ V)

open scoped BigOperators in
theorem rsFintype_sum_if_mem_const
    {α : Type} [Fintype α] [DecidableEq α]
    (B : Finset α) (c : ℝ) :
    (∑ i : α, if i ∈ B then c else 0) = (B.card : ℝ) * c := by
  rw [Finset.sum_ite_mem_eq]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.cast_id]

noncomputable def rsFixedPatternBound (q t n k r : ℕ) : ℝ :=
  (Nat.choose n r : ℝ) * (2 : ℝ) ^ (t * r) *
    (((((t - 1) * k : ℕ) : ℝ) / ((q : ℝ) - n)) ^ r)

def rsIndexedGZP {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (S : ι → Finset (Fin n)) : Prop :=
  ∀ K : Finset ι, K.Nonempty →
    (Finset.univ.filter fun i => ∀ a ∈ K, i ∈ S a).card + K.card ≤
      Fintype.card ι

noncomputable def rsOrientationEnterEdges {t n : ℕ}
    (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (U : Finset (Fin t)) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    O.head i (hE i) ∈ U ∧ (H i \ U).Nonempty

def rsOrientationCoversDemand {t n : ℕ}
    (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (p : Finset (Fin t) → ℕ) : Prop :=
  ∀ U : Finset (Fin t),
    p U ≤ (rsOrientationEnterEdges H O hE U).card

noncomputable def rsOrientationExitEdges {t n : ℕ}
    (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (K : Finset (Fin t)) :
    Finset (Fin n) :=
  Finset.univ.filter fun i =>
    O.head i (hE i) ∉ K ∧ (H i ∩ K).Nonempty

structure RSRootedCutOrientation {t n : ℕ}
    (H : RSAgreementPattern t n) (k : ℕ) where
  orientation : RSOrientation H
  root : Fin t
  edge_nonempty : ∀ i, (H i).Nonempty
  cut_bound : ∀ K : Finset (Fin t), K.Nonempty → root ∉ K →
    k ≤ (rsOrientationExitEdges H orientation edge_nonempty K).card

theorem rsOrientationEnterEdges_compl_eq_exitEdges
    {t n : ℕ} (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (K : Finset (Fin t)) :
    rsOrientationEnterEdges H O hE
        ((Finset.univ : Finset (Fin t)) \ K) =
      rsOrientationExitEdges H O hE K := by
  classical
  ext i
  simp only [rsOrientationEnterEdges, rsOrientationExitEdges,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨(Finset.mem_sdiff.mp h.1).2, ?_⟩
    rcases h.2 with ⟨x, hx⟩
    have hxmem := Finset.mem_sdiff.mp hx
    have hxK : x ∈ K := by
      by_contra hxnotK
      apply hxmem.2
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxnotK⟩
    exact ⟨x, Finset.mem_inter.mpr ⟨hxmem.1, hxK⟩⟩
  · intro h
    refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h.1⟩, ?_⟩
    rcases h.2 with ⟨x, hx⟩
    have hxmem := Finset.mem_inter.mp hx
    refine ⟨x, Finset.mem_sdiff.mpr ⟨hxmem.1, ?_⟩⟩
    intro hxcompl
    exact (Finset.mem_sdiff.mp hxcompl).2 hxmem.2

noncomputable def rsOrientationHeadInEdges {t n : ℕ}
    (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (U : Finset (Fin t)) : Finset (Fin n) :=
  Finset.univ.filter fun i => O.head i (hE i) ∈ U

theorem rsOrientationExitEdges_subset_headIn_compl
    {t n : ℕ} (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (K : Finset (Fin t)) :
    rsOrientationExitEdges H O hE K ⊆
      rsOrientationHeadInEdges H O hE
        ((Finset.univ : Finset (Fin t)) \ K) := by
  intro i hi
  rw [rsOrientationExitEdges] at hi
  rw [rsOrientationHeadInEdges]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact hi.1

noncomputable def rsOrientationIndegree {t n : ℕ}
    (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (v : Fin t) : ℕ :=
  (Finset.univ.filter fun i => O.head i (hE i) = v).card

open scoped BigOperators in
theorem rsOrientationHeadInEdges_card {t n : ℕ}
    (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (U : Finset (Fin t)) :
    (rsOrientationHeadInEdges H O hE U).card =
      ∑ v ∈ U, rsOrientationIndegree H O hE v := by
  classical
  symm
  simpa only [rsOrientationHeadInEdges, rsOrientationIndegree] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (s := (Finset.univ : Finset (Fin n))) (t := U)
      (fun i => O.head i (hE i)))

open scoped BigOperators in
theorem rsOrientationIndegree_sum {t n : ℕ}
    (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) :
    ∑ v : Fin t, rsOrientationIndegree H O hE v = n := by
  classical
  simpa only [rsOrientationIndegree, Finset.mem_univ, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin t)))
      (fun i => O.head i (hE i)))

def rsPathsEdgeDisjoint {t n k : ℕ} {H : RSAgreementPattern t n}
    {O : RSOrientation H} {start finish : Fin t}
    (paths : Fin k → RSDirectedPath H O start finish) : Prop :=
  ∀ a b, a ≠ b →
    Disjoint (rsDirectedPathEdges (paths a)) (rsDirectedPathEdges (paths b))

structure RSRootedPathOrientation {t n k : ℕ}
    (H : RSAgreementPattern t n) where
  orientation : RSOrientation H
  root : Fin t
  edge_nonempty : ∀ i, (H i).Nonempty
  paths : ∀ v : Fin t, v ≠ root →
    Fin k → RSDirectedPath H orientation v root
  paths_edgeDisjoint : ∀ (v : Fin t) (hv : v ≠ root),
    rsPathsEdgeDisjoint (paths v hv)

open scoped BigOperators in
noncomputable def rsPatternCrossingWeightOn {t n : ℕ}
    (H : RSAgreementPattern t n) {J : Finset (Fin t)} (P : Finpartition J) : ℝ :=
  ∑ i : Fin n,
    max (((P.parts.filter (fun A => (A ∩ H i).Nonempty)).card : ℝ) - 1) 0

open scoped BigOperators in
theorem rsPatternCrossingWeightOn_nonneg {t n : ℕ}
    (H : RSAgreementPattern t n) {J : Finset (Fin t)} (P : Finpartition J) :
    0 ≤ rsPatternCrossingWeightOn H P := by
  unfold rsPatternCrossingWeightOn
  apply Finset.sum_nonneg
  intro i hi
  exact le_max_right _ _

noncomputable def rsPatternEraseCoordinates {t n : ℕ}
    (H : RSAgreementPattern t n) (B : Finset (Fin n)) :
    RSAgreementPattern t n :=
  fun i => if i ∈ B then ∅ else H i

theorem rsPatternErase_mem_iff {t n : ℕ}
    (H : RSAgreementPattern t n) (B : Finset (Fin n))
    (i : Fin n) (v : Fin t) :
    v ∈ rsPatternEraseCoordinates H B i ↔ i ∉ B ∧ v ∈ H i := by
  unfold rsPatternEraseCoordinates
  by_cases hi : i ∈ B
  · simp only [hi, if_true, Finset.notMem_empty, false_and,
      not_true_eq_false, iff_false]
  · simp only [hi, if_false, not_false_eq_true, true_and]

noncomputable def rsPatternErase_rimRowEmbedding {t n : ℕ}
    (H : RSAgreementPattern t n) (B : Finset (Fin n)) :
    RSRIMRow (rsPatternEraseCoordinates H B) ↪ RSRIMRow H where
  toFun r := by
    have ha := (rsPatternErase_mem_iff H B r.1.1 r.1.2.1).mp r.2.1
    have hb := (rsPatternErase_mem_iff H B r.1.1 r.1.2.2).mp r.2.2.1
    refine ⟨r.1, ha.2, hb.2, r.2.2.2.1, ?_⟩
    intro u hu
    apply r.2.2.2.2 u
    exact (rsPatternErase_mem_iff H B r.1.1 u).mpr ⟨ha.1, hu⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    change a.1 = b.1
    exact congrArg (fun r : RSRIMRow H => r.1) hab

theorem rsPatternErase_rimRowEmbedding_coord_notMem {t n : ℕ}
    (H : RSAgreementPattern t n) (B : Finset (Fin n))
    (r : RSRIMRow (rsPatternEraseCoordinates H B)) :
    (rsPatternErase_rimRowEmbedding H B r).1.1 ∉ B := by
  have hr := (rsPatternErase_mem_iff H B r.1.1 r.1.2.1).mp r.2.1
  exact hr.1

noncomputable def rsPatternFillEmpty {t n : ℕ}
    (H : RSAgreementPattern t n) (fallback : Fin t) :
    RSAgreementPattern t n :=
  fun i => if (H i).Nonempty then H i else {fallback}

theorem rsPatternFillEmpty_crossingTerm
    {t n : ℕ} (H : RSAgreementPattern t n) (fallback : Fin t)
    (P : Finpartition (Finset.univ : Finset (Fin t))) (i : Fin n) :
    max ((((P.parts.filter fun A =>
      (A ∩ rsPatternFillEmpty H fallback i).Nonempty).card : ℝ) - 1)) 0 =
      max ((((P.parts.filter fun A =>
        (A ∩ H i).Nonempty).card : ℝ) - 1)) 0 := by
  classical
  by_cases h : (H i).Nonempty
  · rw [rsPatternFillEmpty, if_pos h]
  · have he : H i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [rsPatternFillEmpty, if_neg h, he]
    rw [rsFinpartition_touched_singleton_card P fallback
      (Finset.mem_univ fallback)]
    simp only [Finset.inter_empty, Finset.not_nonempty_empty,
      Finset.filter_false, Finset.card_empty]
    norm_num

open scoped BigOperators in
theorem rsPatternCrossingWeight_fillEmpty
    {t n : ℕ} (H : RSAgreementPattern t n) (fallback : Fin t)
    (P : Finpartition (Finset.univ : Finset (Fin t))) :
    (∑ i : Fin n,
      max ((((P.parts.filter fun A =>
        (A ∩ rsPatternFillEmpty H fallback i).Nonempty).card : ℝ) - 1)) 0) =
      ∑ i : Fin n,
        max ((((P.parts.filter fun A =>
          (A ∩ H i).Nonempty).card : ℝ) - 1)) 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  exact rsPatternFillEmpty_crossingTerm H fallback P i

theorem rsPatternFillEmpty_nonempty {t n : ℕ}
    (H : RSAgreementPattern t n) (fallback : Fin t) (i : Fin n) :
    (rsPatternFillEmpty H fallback i).Nonempty := by
  unfold rsPatternFillEmpty
  split_ifs with h
  · exact h
  · exact Finset.singleton_nonempty fallback

theorem rsPatternFillEmpty_pair_mem_iff {t n : ℕ}
    (H : RSAgreementPattern t n) (fallback : Fin t)
    (i : Fin n) {a b : Fin t} (hab : a ≠ b) :
    (a ∈ rsPatternFillEmpty H fallback i ∧
      b ∈ rsPatternFillEmpty H fallback i) ↔
    (a ∈ H i ∧ b ∈ H i) := by
  by_cases h : (H i).Nonempty
  · rw [rsPatternFillEmpty, if_pos h]
  · have he : H i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [rsPatternFillEmpty, if_neg h, he]
    simp only [Finset.mem_singleton, Finset.notMem_empty, false_and, iff_false]
    rintro ⟨ha, hb⟩
    exact hab (ha.trans hb.symm)

noncomputable def rsPatternFillEmpty_rimRowEquiv
    {t n : ℕ} (H : RSAgreementPattern t n) (fallback : Fin t) :
    RSRIMRow (rsPatternFillEmpty H fallback) ≃ RSRIMRow H where
  toFun r := by
    have hab : r.1.2.1 ≠ r.1.2.2 := ne_of_lt r.2.2.2.1
    have hp := (rsPatternFillEmpty_pair_mem_iff
      H fallback r.1.1 hab).mp ⟨r.2.1, r.2.2.1⟩
    refine ⟨r.1, hp.1, hp.2, r.2.2.2.1, ?_⟩
    intro u hu
    apply r.2.2.2.2 u
    rw [rsPatternFillEmpty, if_pos ⟨u, hu⟩]
    exact hu
  invFun r := by
    have hab : r.1.2.1 ≠ r.1.2.2 := ne_of_lt r.2.2.2.1
    have hp := (rsPatternFillEmpty_pair_mem_iff
      H fallback r.1.1 hab).mpr ⟨r.2.1, r.2.2.1⟩
    refine ⟨r.1, hp.1, hp.2, r.2.2.2.1, ?_⟩
    intro u hu
    have hE : (H r.1.1).Nonempty := ⟨r.1.2.1, r.2.1⟩
    rw [rsPatternFillEmpty, if_pos hE] at hu
    exact r.2.2.2.2 u hu
  left_inv r := by
    apply Subtype.ext
    rfl
  right_inv r := by
    apply Subtype.ext
    rfl

def rsPatternInternalEdges {t n : ℕ} (H : RSAgreementPattern t n)
    (U : Finset (Fin t)) : Finset (Fin n) :=
  Finset.univ.filter fun i => H i ⊆ U

theorem rsPatternInternalEdges_disjoint_exitEdges
    {t n : ℕ} (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (K : Finset (Fin t)) :
    Disjoint
      (rsPatternInternalEdges H
        ((Finset.univ : Finset (Fin t)) \ K))
      (rsOrientationExitEdges H O hE K) := by
  rw [Finset.disjoint_left]
  intro i hiInternal hiExit
  rw [rsPatternInternalEdges] at hiInternal
  rw [rsOrientationExitEdges] at hiExit
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiInternal hiExit
  obtain ⟨v, hv⟩ := hiExit.2
  have hvCompl := hiInternal (Finset.mem_inter.mp hv).1
  exact (Finset.mem_sdiff.mp hvCompl).2 (Finset.mem_inter.mp hv).2

theorem rsPatternInternalEdges_subset_headInEdges
    {t n : ℕ} (H : RSAgreementPattern t n) (O : RSOrientation H)
    (hE : ∀ i, (H i).Nonempty) (U : Finset (Fin t)) :
    rsPatternInternalEdges H U ⊆ rsOrientationHeadInEdges H O hE U := by
  intro i hi
  rw [rsPatternInternalEdges] at hi
  rw [rsOrientationHeadInEdges]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi (O.head_mem i (hE i))

noncomputable def rsPatternOccurs {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (t n k : ℕ) (H : RSAgreementPattern t n) (α : Fin n ↪ F) : Prop :=
  ∃ p : Fin t → Polynomial F,
    Function.Injective p ∧ (∀ j, (p j).degree < k) ∧
      ∃ y : Fin n → F, ∀ i j, j ∈ H i ↔ (p j).eval (α i) = y i

noncomputable def rsFixedPatternBadEmbeddings
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (t n k : ℕ) (H : RSAgreementPattern t n) : Finset (Fin n ↪ F) := by
  classical
  exact Finset.univ.filter (rsPatternOccurs t n k H)

noncomputable def rsAllPatternBadEmbeddings
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) : Finset (Fin n ↪ F) := by
  classical
  exact (Finset.Icc 2 (ℓ + 1)).biUnion fun t =>
    (Finset.univ : Finset (RSAgreementPattern t n)).biUnion fun H =>
      rsFixedPatternBadEmbeddings (F := F) t n k H

def rsPatternPermute {t n : ℕ} (H : RSAgreementPattern t n)
    (σ : Equiv.Perm (Fin n)) : RSAgreementPattern t n :=
  fun i => H (σ i)

theorem rsPatternPermute_occurs
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {t n k : ℕ} (H : RSAgreementPattern t n)
    (σ : Equiv.Perm (Fin n)) (α : Fin n ↪ F)
    (hocc : rsPatternOccurs t n k H α) :
    rsPatternOccurs t n k (rsPatternPermute H σ)
      (σ.toEmbedding.trans α) := by
  rcases hocc with ⟨p, hp_inj, hp_deg, y, hy⟩
  refine ⟨p, hp_inj, hp_deg, fun i => y (σ i), ?_⟩
  intro i j
  change j ∈ H (σ i) ↔ (p j).eval (α (σ i)) = y (σ i)
  exact hy (σ i) j

noncomputable def rsPatternRestrict {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t)) :
    RSAgreementPattern J.card n :=
  fun i => Finset.univ.filter fun j : Fin J.card =>
    (((Finset.equivFin J).symm j : J) : Fin t) ∈ H i

noncomputable def rsPatternRestrictEmbedding {t : ℕ}
    (J : Finset (Fin t)) : Fin J.card ↪ Fin t :=
  ((Finset.equivFin J).symm.toEmbedding).trans
    (Function.Embedding.subtype (fun x : Fin t => x ∈ J))

noncomputable def rsPatternPushPart {t : ℕ} (J : Finset (Fin t))
    (A : Finset (Fin J.card)) : Finset (Fin t) :=
  A.map (rsPatternRestrictEmbedding J)

theorem rsPatternPushPart_card {t : ℕ} (J : Finset (Fin t))
    (A : Finset (Fin J.card)) :
    (rsPatternPushPart J A).card = A.card := by
  unfold rsPatternPushPart
  exact Finset.card_map (s := A) (rsPatternRestrictEmbedding J)

theorem rsPatternPushPart_injective {t : ℕ} (J : Finset (Fin t)) :
    Function.Injective (rsPatternPushPart J) := by
  unfold rsPatternPushPart
  exact Finset.map_injective (rsPatternRestrictEmbedding J)

theorem rsPatternPushPart_mem {t : ℕ} (J : Finset (Fin t))
    (A : Finset (Fin J.card)) (j : Fin J.card) :
    rsPatternRestrictEmbedding J j ∈ rsPatternPushPart J A ↔ j ∈ A := by
  unfold rsPatternPushPart
  exact Finset.mem_map' (rsPatternRestrictEmbedding J)

theorem rsPatternPushPart_nonempty {t : ℕ} (J : Finset (Fin t))
    (A : Finset (Fin J.card)) :
    (rsPatternPushPart J A).Nonempty ↔ A.Nonempty := by
  unfold rsPatternPushPart
  exact Finset.map_nonempty

theorem rsPatternPushPart_subset {t : ℕ} (J : Finset (Fin t))
    (A : Finset (Fin J.card)) :
    rsPatternPushPart J A ⊆ J := by
  intro x hx
  rw [rsPatternPushPart] at hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
  change ((((Finset.equivFin J).symm j : J) : Fin t) ∈ J)
  exact ((Finset.equivFin J).symm j : J).property

@[simp] theorem rsPatternRestrictEmbedding_apply {t : ℕ}
    (J : Finset (Fin t)) (j : Fin J.card) :
    rsPatternRestrictEmbedding J j =
      (((Finset.equivFin J).symm j : J) : Fin t) := rfl

theorem rsPatternRestrictEmbedding_univ_map {t : ℕ}
    (J : Finset (Fin t)) :
    Finset.univ.map (rsPatternRestrictEmbedding J) = J := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
    exact ((Finset.equivFin J).symm j : J).property
  · intro hx
    let j : Fin J.card := Finset.equivFin J ⟨x, hx⟩
    apply Finset.mem_map.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    simp only [j, rsPatternRestrictEmbedding_apply, Equiv.symm_apply_apply,
      Subtype.coe_eta]

noncomputable def rsFinpartitionPushRestrict {t : ℕ}
    (J : Finset (Fin t))
    (P : Finpartition (Finset.univ : Finset (Fin J.card))) :
    Finpartition J := by
  classical
  let f : Finset (Fin J.card) ↪ Finset (Fin t) :=
    ⟨rsPatternPushPart J, rsPatternPushPart_injective J⟩
  apply Finpartition.ofExistsUnique (P.parts.map f)
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hA
    exact rsPatternPushPart_subset J B
  · intro x hx
    have hxmap : x ∈ Finset.univ.map (rsPatternRestrictEmbedding J) := by
      rw [rsPatternRestrictEmbedding_univ_map]
      exact hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hxmap
    obtain ⟨A, hA, huniq⟩ := P.existsUnique_mem (Finset.mem_univ j)
    refine ⟨rsPatternPushPart J A, ?_, ?_⟩
    · exact ⟨Finset.mem_map.mpr ⟨A, hA.1, rfl⟩,
        (rsPatternPushPart_mem J A j).2 hA.2⟩
    · intro B hB
      obtain ⟨C, hC, rfl⟩ := Finset.mem_map.mp hB.1
      apply congrArg (rsPatternPushPart J)
      exact huniq C ⟨hC, (rsPatternPushPart_mem J C j).1 hB.2⟩
  · intro hempty
    obtain ⟨A, hA, hmap⟩ := Finset.mem_map.mp hempty
    have hne : (rsPatternPushPart J A).Nonempty :=
      (rsPatternPushPart_nonempty J A).2 (P.nonempty_of_mem_parts hA)
    change rsPatternPushPart J A = ∅ at hmap
    rw [hmap] at hne
    exact Finset.not_nonempty_empty hne

theorem rsFinpartitionPushRestrict_parts {t : ℕ}
    (J : Finset (Fin t))
    (P : Finpartition (Finset.univ : Finset (Fin J.card))) :
    (rsFinpartitionPushRestrict J P).parts =
      P.parts.map
        ⟨rsPatternPushPart J, rsPatternPushPart_injective J⟩ := by
  classical
  unfold rsFinpartitionPushRestrict
  apply Finpartition.ofExistsUnique_parts

theorem rsFinpartitionPushRestrict_parts_card {t : ℕ}
    (J : Finset (Fin t))
    (P : Finpartition (Finset.univ : Finset (Fin J.card))) :
    (rsFinpartitionPushRestrict J P).parts.card = P.parts.card := by
  rw [rsFinpartitionPushRestrict_parts]
  exact Finset.card_map (s := P.parts)
    ⟨rsPatternPushPart J, rsPatternPushPart_injective J⟩

theorem rsPatternRestrict_mem_iff {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t))
    (i : Fin n) (j : Fin J.card) :
    j ∈ rsPatternRestrict H J i ↔
      ((((Finset.equivFin J).symm j : J) : Fin t) ∈ H i) := by
  unfold rsPatternRestrict
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem rsPatternOccurs_restrict
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {t n k : ℕ} (H : RSAgreementPattern t n) (J : Finset (Fin t))
    (α : Fin n ↪ F) (hocc : rsPatternOccurs t n k H α) :
    rsPatternOccurs J.card n k (rsPatternRestrict H J) α := by
  classical
  rcases hocc with ⟨p, hp_inj, hp_deg, y, hy⟩
  let e : Fin J.card → Fin t := fun j => (((Finset.equivFin J).symm j : J) : Fin t)
  refine ⟨fun j => p (e j), ?_, ?_, y, ?_⟩
  · intro a b hab
    have he : e a = e b := hp_inj hab
    apply (Finset.equivFin J).symm.injective
    exact Subtype.ext he
  · intro j
    exact hp_deg (e j)
  · intro i j
    rw [rsPatternRestrict_mem_iff]
    exact hy i (e j)

theorem rsPatternRestrict_mem_iff_embedding {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t))
    (i : Fin n) (j : Fin J.card) :
    j ∈ rsPatternRestrict H J i ↔
      rsPatternRestrictEmbedding J j ∈ H i := by
  simpa only [rsPatternRestrictEmbedding_apply] using
    rsPatternRestrict_mem_iff H J i j

theorem rsPatternPushPart_inter_nonempty_iff {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t))
    (A : Finset (Fin J.card)) (i : Fin n) :
    (rsPatternPushPart J A ∩ H i).Nonempty ↔
      (A ∩ rsPatternRestrict H J i).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    have hxmap : x ∈ A.map (rsPatternRestrictEmbedding J) := by
      simpa only [rsPatternPushPart] using (Finset.mem_inter.mp hx).1
    obtain ⟨j, hj, hjx⟩ := Finset.mem_map.mp hxmap
    refine ⟨j, Finset.mem_inter.mpr ⟨hj, ?_⟩⟩
    rw [rsPatternRestrict_mem_iff_embedding]
    rw [hjx]
    exact (Finset.mem_inter.mp hx).2
  · rintro ⟨j, hj⟩
    refine ⟨rsPatternRestrictEmbedding J j, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact (rsPatternPushPart_mem J A j).2 (Finset.mem_inter.mp hj).1
    · exact (rsPatternRestrict_mem_iff_embedding H J i j).1
        (Finset.mem_inter.mp hj).2

theorem rsFinpartitionPushRestrict_touched_card {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t))
    (P : Finpartition (Finset.univ : Finset (Fin J.card))) (i : Fin n) :
    ((rsFinpartitionPushRestrict J P).parts.filter
      (fun B => (B ∩ H i).Nonempty)).card =
    (P.parts.filter
      (fun A => (A ∩ rsPatternRestrict H J i).Nonempty)).card := by
  classical
  rw [rsFinpartitionPushRestrict_parts, Finset.filter_map]
  rw [Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro A hA
  change (rsPatternPushPart J A ∩ H i).Nonempty ↔
    (A ∩ rsPatternRestrict H J i).Nonempty
  exact rsPatternPushPart_inter_nonempty_iff H J A i

open scoped BigOperators in
theorem rsPatternCrossingWeightOn_push_restrict {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t))
    (P : Finpartition (Finset.univ : Finset (Fin J.card))) :
    rsPatternCrossingWeightOn H (rsFinpartitionPushRestrict J P) =
      rsPatternCrossingWeightOn (rsPatternRestrict H J) P := by
  unfold rsPatternCrossingWeightOn
  apply Finset.sum_congr rfl
  intro i hi
  rw [rsFinpartitionPushRestrict_touched_card H J P i]

open scoped BigOperators in
noncomputable def rsPatternSubsetWeight {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t)) : ℝ :=
  ∑ i : Fin n, max (((J ∩ H i).card : ℝ) - 1) 0

open scoped BigOperators in
theorem rsPatternSubsetWeight_eq_zero_of_card_le_one {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t))
    (hJ : J.card ≤ 1) :
    rsPatternSubsetWeight H J = 0 := by
  classical
  unfold rsPatternSubsetWeight
  apply Finset.sum_eq_zero
  intro i hi
  rw [max_eq_right]
  have hcardNat : (J ∩ H i).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans hJ
  exact sub_nonpos.mpr (by exact_mod_cast hcardNat)

open scoped BigOperators in
theorem rsPatternSubsetWeight_nonneg {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t)) :
    0 ≤ rsPatternSubsetWeight H J := by
  unfold rsPatternSubsetWeight
  apply Finset.sum_nonneg
  intro i hi
  exact le_max_right _ _

open scoped BigOperators in
theorem rsPatternSubsetWeight_univ_ge_sum_card_sub {t n : ℕ}
    (H : RSAgreementPattern t n) :
    (∑ i : Fin n, ((H i).card : ℝ)) - (n : ℝ) ≤
      rsPatternSubsetWeight H (Finset.univ : Finset (Fin t)) := by
  classical
  unfold rsPatternSubsetWeight
  have hn : (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
  rw [hn, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [Finset.univ_inter]
  exact le_max_left _ _

noncomputable def rsPatternTouchedParts {t n : ℕ}
    (H : RSAgreementPattern t n)
    (P : Finpartition (Finset.univ : Finset (Fin t))) (i : Fin n) :
    Finset (Finset (Fin t)) :=
  P.parts.filter fun A => (A ∩ H i).Nonempty

noncomputable def rsPatternCrossingEdges {t n : ℕ}
    (H : RSAgreementPattern t n)
    (P : Finpartition (Finset.univ : Finset (Fin t))) : Finset (Fin n) :=
  Finset.univ.filter fun i => 2 ≤ (rsPatternTouchedParts H P i).card

open scoped BigOperators in
noncomputable def rsPatternCrossingWeightNat {t n : ℕ}
    (H : RSAgreementPattern t n)
    (P : Finpartition (Finset.univ : Finset (Fin t))) : ℕ :=
  ∑ i : Fin n, ((rsPatternTouchedParts H P i).card - 1)

open scoped BigOperators in
theorem rsPatternCrossingWeightNat_cast {t n : ℕ}
    (H : RSAgreementPattern t n)
    (P : Finpartition (Finset.univ : Finset (Fin t))) :
    (rsPatternCrossingWeightNat H P : ℝ) =
      rsPatternCrossingWeightOn H P := by
  classical
  unfold rsPatternCrossingWeightNat rsPatternCrossingWeightOn
  calc
    ((∑ i : Fin n, ((rsPatternTouchedParts H P i).card - 1) : ℕ) : ℝ) =
        ∑ i : Fin n, (((rsPatternTouchedParts H P i).card - 1 : ℕ) : ℝ) := by
      norm_cast
    _ = ∑ i : Fin n,
        max ((((P.parts.filter fun A => (A ∩ H i).Nonempty).card : ℝ) - 1)) 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold rsPatternTouchedParts
      let m := (P.parts.filter fun A => (A ∩ H i).Nonempty).card
      change ((m - 1 : ℕ) : ℝ) = max ((m : ℝ) - 1) 0
      by_cases hm : m = 0
      · simp only [hm, Nat.zero_sub, Nat.cast_zero, zero_sub]
        norm_num
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        rw [Nat.cast_sub hm1]
        rw [max_eq_left (sub_nonneg.mpr hm1R)]
        norm_num

open scoped BigOperators in
noncomputable def rsPatternWeaklyPartitionConnected (κ : ℝ) {t n : ℕ}
    (H : RSAgreementPattern t n) : Prop :=
  ∀ P : Finpartition (Finset.univ : Finset (Fin t)),
    κ * ((P.parts.card : ℝ) - 1) ≤
      ∑ i : Fin n,
        max (((P.parts.filter (fun A => (A ∩ H i).Nonempty)).card : ℝ) - 1) 0

noncomputable def rsBadOrderedEmbedding
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (α : Fin n ↪ F) : Prop :=
  ∃ t : ℕ, 2 ≤ t ∧ t ≤ ℓ + 1 ∧
    ∃ H : RSAgreementPattern t n,
      rsPatternWeaklyPartitionConnected ((k : ℝ) + η * (n : ℝ)) H ∧
        rsPatternOccurs t n k H α

noncomputable def rsBadOrderedEmbeddings
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) : Finset (Fin n ↪ F) := by
  classical
  exact Finset.univ.filter (rsBadOrderedEmbedding ℓ k n η)

theorem rsBadOrderedEmbeddings_subset_allPattern
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) :
    rsBadOrderedEmbeddings (F := F) ℓ k n η ⊆
      rsAllPatternBadEmbeddings (F := F) ℓ k n := by
  classical
  intro α hα
  rw [rsBadOrderedEmbeddings, Finset.mem_filter] at hα
  rcases hα.2 with ⟨t, ht, htℓ, H, _hWPC, hocc⟩
  rw [rsAllPatternBadEmbeddings]
  apply Finset.mem_biUnion.mpr
  refine ⟨t, Finset.mem_Icc.mpr ⟨ht, htℓ⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨H, Finset.mem_univ H, ?_⟩
  rw [rsFixedPatternBadEmbeddings, Finset.mem_filter]
  exact ⟨Finset.mem_univ α, hocc⟩

open scoped BigOperators in
theorem rsPatternPermute_wpc
    {t n : ℕ} (H : RSAgreementPattern t n)
    (σ : Equiv.Perm (Fin n)) (κ : ℝ) :
    rsPatternWeaklyPartitionConnected κ (rsPatternPermute H σ) ↔
      rsPatternWeaklyPartitionConnected κ H := by
  unfold rsPatternWeaklyPartitionConnected rsPatternPermute
  constructor
  · intro h P
    let g : Fin n → ℝ := fun i =>
      max (((P.parts.filter
        (fun A => (A ∩ H i).Nonempty)).card : ℝ) - 1) 0
    have hP := h P
    change κ * ((P.parts.card : ℝ) - 1) ≤ ∑ i : Fin n, g (σ i) at hP
    change κ * ((P.parts.card : ℝ) - 1) ≤ ∑ i : Fin n, g i
    exact hP.trans_eq (Equiv.sum_comp σ g)
  · intro h P
    let g : Fin n → ℝ := fun i =>
      max (((P.parts.filter
        (fun A => (A ∩ H i).Nonempty)).card : ℝ) - 1) 0
    have hP := h P
    change κ * ((P.parts.card : ℝ) - 1) ≤ ∑ i : Fin n, g i at hP
    change κ * ((P.parts.card : ℝ) - 1) ≤ ∑ i : Fin n, g (σ i)
    exact hP.trans_eq (Equiv.sum_comp σ g).symm

theorem rsBadOrderedEmbedding_precomp_perm
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} (α : Fin n ↪ F)
    (σ : Equiv.Perm (Fin n))
    (hbad : rsBadOrderedEmbedding ℓ k n η α) :
    rsBadOrderedEmbedding ℓ k n η (σ.toEmbedding.trans α) := by
  rcases hbad with ⟨t, ht, htℓ, H, hWPC, hocc⟩
  refine ⟨t, ht, htℓ, rsPatternPermute H σ, ?_, ?_⟩
  · exact (rsPatternPermute_wpc H σ
      ((k : ℝ) + η * (n : ℝ))).2 hWPC
  · exact rsPatternPermute_occurs H σ α hocc

open scoped BigOperators in
noncomputable def rsPatternWeaklyPartitionConnectedOn (κ : ℝ) {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t)) : Prop :=
  ∀ P : Finpartition J,
    κ * ((P.parts.card : ℝ) - 1) ≤ rsPatternCrossingWeightOn H P

open scoped BigOperators in
theorem rsPatternWeaklyPartitionConnected_fillEmpty
    {t n : ℕ} (H : RSAgreementPattern t n) (fallback : Fin t)
    (κ : ℝ) :
    rsPatternWeaklyPartitionConnected κ (rsPatternFillEmpty H fallback) ↔
      rsPatternWeaklyPartitionConnected κ H := by
  unfold rsPatternWeaklyPartitionConnected
  constructor
  · intro h P
    have hP := h P
    rw [rsPatternCrossingWeight_fillEmpty H fallback P] at hP
    exact hP
  · intro h P
    have hP := h P
    rw [rsPatternCrossingWeight_fillEmpty H fallback P]
    exact hP

theorem rsPatternWeaklyPartitionConnected_mono
    {t n : ℕ} (H : RSAgreementPattern t n) (ht : 1 ≤ t)
    {κ₁ κ₂ : ℝ} (hκ : κ₁ ≤ κ₂)
    (hWPC : rsPatternWeaklyPartitionConnected κ₂ H) :
    rsPatternWeaklyPartitionConnected κ₁ H := by
  intro P
  have htpos : 0 < t := by omega
  have huniv : (Finset.univ : Finset (Fin t)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by
      simpa only [Fintype.card_fin] using htpos))
  have hparts : P.parts.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by
      intro hempty
      have hu := huniv
      have hJempty := P.parts_eq_empty_iff.mp hempty
      rw [hJempty] at hu
      exact Finset.not_nonempty_empty hu)
  have hfactor : 0 ≤ (P.parts.card : ℝ) - 1 := by
    have hcard : 1 ≤ P.parts.card := Finset.one_le_card.mpr hparts
    exact sub_nonneg.mpr (by exact_mod_cast hcard)
  exact (mul_le_mul_of_nonneg_right hκ hfactor).trans (hWPC P)

open scoped BigOperators in
theorem rsPatternWeaklyPartitionConnected_restrict {t n : ℕ}
    (H : RSAgreementPattern t n) (J : Finset (Fin t)) (κ : ℝ)
    (h : rsPatternWeaklyPartitionConnectedOn κ H J) :
    rsPatternWeaklyPartitionConnected κ (rsPatternRestrict H J) := by
  unfold rsPatternWeaklyPartitionConnected
  intro P
  change κ * ((P.parts.card : ℝ) - 1) ≤
    rsPatternCrossingWeightOn (rsPatternRestrict H J) P
  have hQ := h (rsFinpartitionPushRestrict J P)
  rw [rsFinpartitionPushRestrict_parts_card,
    rsPatternCrossingWeightOn_push_restrict] at hQ
  exact hQ

theorem rsPattern_crossingTerm_le_parts_sub_one
    {t n : ℕ} (H : RSAgreementPattern t n) (ht : 0 < t)
    (P : Finpartition (Finset.univ : Finset (Fin t))) (i : Fin n) :
    max (((P.parts.filter fun A => (A ∩ H i).Nonempty).card : ℝ) - 1) 0 ≤
      (P.parts.card : ℝ) - 1 := by
  have hparts : 1 ≤ P.parts.card :=
    Finset.one_le_card.mpr (rsFinpartition_parts_nonempty_of_fin_pos ht P)
  apply max_le
  · apply sub_le_sub_right
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  · exact sub_nonneg.mpr (by exact_mod_cast hparts)

open scoped BigOperators in
theorem rsPatternErase_crossingWeight_lower
    {t n : ℕ} (H : RSAgreementPattern t n)
    (B : Finset (Fin n)) (ht : 0 < t)
    (P : Finpartition (Finset.univ : Finset (Fin t))) :
    rsPatternCrossingWeightOn H P ≤
      rsPatternCrossingWeightOn (rsPatternEraseCoordinates H B) P +
        (B.card : ℝ) * ((P.parts.card : ℝ) - 1) := by
  classical
  unfold rsPatternCrossingWeightOn
  calc
    (∑ i : Fin n,
        max (((P.parts.filter fun A => (A ∩ H i).Nonempty).card : ℝ) - 1) 0) ≤
        ∑ i : Fin n,
          (max (((P.parts.filter fun A =>
              (A ∩ rsPatternEraseCoordinates H B i).Nonempty).card : ℝ) - 1) 0 +
            if i ∈ B then ((P.parts.card : ℝ) - 1) else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiB : i ∈ B
      · rw [rsPatternEraseCoordinates, if_pos hiB]
        simp only [Finset.inter_empty, Finset.not_nonempty_empty,
          Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_sub]
        rw [max_eq_right (by norm_num : (-1 : ℝ) ≤ 0)]
        simp only [hiB, if_true, zero_add]
        exact rsPattern_crossingTerm_le_parts_sub_one H ht P i
      · rw [rsPatternEraseCoordinates, if_neg hiB]
        simp only [hiB, if_false, add_zero]
        exact le_rfl
    _ = (∑ i : Fin n,
          max (((P.parts.filter fun A =>
            (A ∩ rsPatternEraseCoordinates H B i).Nonempty).card : ℝ) - 1) 0) +
        ∑ i : Fin n,
          if i ∈ B then ((P.parts.card : ℝ) - 1) else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin n,
          max (((P.parts.filter fun A =>
            (A ∩ rsPatternEraseCoordinates H B i).Nonempty).card : ℝ) - 1) 0) +
        (B.card : ℝ) * ((P.parts.card : ℝ) - 1) := by
      rw [rsFintype_sum_if_mem_const]

open scoped BigOperators in
theorem rsPatternErase_preserves_wpc
    {t n : ℕ} (H : RSAgreementPattern t n)
    (B : Finset (Fin n)) (ht : 0 < t) (κ : ℝ)
    (hWPC : rsPatternWeaklyPartitionConnected
      (κ + (B.card : ℝ)) H) :
    rsPatternWeaklyPartitionConnected κ
      (rsPatternEraseCoordinates H B) := by
  unfold rsPatternWeaklyPartitionConnected at hWPC ⊢
  intro P
  have hconn := hWPC P
  change (κ + (B.card : ℝ)) * ((P.parts.card : ℝ) - 1) ≤
    rsPatternCrossingWeightOn H P at hconn
  change κ * ((P.parts.card : ℝ) - 1) ≤
    rsPatternCrossingWeightOn (rsPatternEraseCoordinates H B) P
  have hloss := rsPatternErase_crossingWeight_lower H B ht P
  nlinarith

open scoped BigOperators in
theorem rsPatternErase_preserves_wpc_of_card_le
    {t n : ℕ} (H : RSAgreementPattern t n)
    (B : Finset (Fin n)) (ht : 0 < t) (κ μ : ℝ)
    (hB : (B.card : ℝ) ≤ μ)
    (hWPC : rsPatternWeaklyPartitionConnected (κ + μ) H) :
    rsPatternWeaklyPartitionConnected κ
      (rsPatternEraseCoordinates H B) := by
  have hparam : κ + (B.card : ℝ) ≤ κ + μ := by linarith
  have hsmall := rsPatternWeaklyPartitionConnected_mono H
    (Nat.succ_le_iff.mpr ht) hparam hWPC
  exact rsPatternErase_preserves_wpc H B ht κ hsmall

open scoped BigOperators in
theorem rsPattern_sum_inter_card_parts {t n : ℕ}
    (H : RSAgreementPattern t n) {J : Finset (Fin t)}
    (P : Finpartition J) (i : Fin n) :
    ∑ A ∈ P.parts, (A ∩ H i).card = (J ∩ H i).card := by
  classical
  have hcount : ∀ a ∈ J ∩ H i,
      (P.parts.filter (fun A => a ∈ A)).card = 1 := by
    intro a ha
    obtain ⟨A, hA, huniq⟩ := P.existsUnique_mem (Finset.mem_inter.mp ha).1
    rw [Finset.card_eq_one]
    refine ⟨A, ?_⟩
    ext B
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hB
      exact huniq B hB
    · intro hBA
      subst B
      exact hA
  have hsum := Finset.sum_card_inter (s := J ∩ H i)
    (B := P.parts) (n := 1) hcount
  simp only [Nat.mul_one] at hsum
  calc
    (∑ A ∈ P.parts, (A ∩ H i).card) =
        ∑ A ∈ P.parts, ((J ∩ H i) ∩ A).card := by
      apply Finset.sum_congr rfl
      intro A hA
      congr 1
      ext x
      simp only [Finset.mem_inter]
      have hAJ := P.le hA
      constructor
      · intro hx
        exact ⟨⟨hAJ hx.1, hx.2⟩, hx.1⟩
      · intro hx
        exact ⟨hx.2, hx.1.2⟩
    _ = (J ∩ H i).card := hsum

noncomputable def rsRIM {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (k : ℕ) :
    Matrix (RSRIMRow H) (RSRIMCol root k) (MvPolynomial (Fin n) F) :=
  fun r c =>
    if c.1.1 = r.1.2.1 then
      MvPolynomial.X r.1.1 ^ (c.2 : ℕ)
    else if c.1.1 = r.1.2.2 then
      -(MvPolynomial.X r.1.1 ^ (c.2 : ℕ))
    else 0

@[simp] theorem rsPatternErase_rim_entry
    {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (B : Finset (Fin n))
    (root : Fin t) (k : ℕ)
    (r : RSRIMRow (rsPatternEraseCoordinates H B))
    (c : RSRIMCol root k) :
    rsRIM (F := F) H root k (rsPatternErase_rimRowEmbedding H B r) c =
      rsRIM (F := F) (rsPatternEraseCoordinates H B) root k r c := by
  rfl

@[simp] theorem rsPatternFillEmpty_rim_entry
    {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (fallback root : Fin t) (k : ℕ)
    (r : RSRIMRow (rsPatternFillEmpty H fallback))
    (c : RSRIMCol root k) :
    rsRIM (F := F) H root k (rsPatternFillEmpty_rimRowEquiv H fallback r) c =
      rsRIM (F := F) (rsPatternFillEmpty H fallback) root k r c := by
  rfl

noncomputable def rsRIMEval {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (k : ℕ)
    (α : Fin n → F) : Matrix (RSRIMRow H) (RSRIMCol root k) F :=
  fun r c => MvPolynomial.eval α (rsRIM (F := F) H root k r c)

noncomputable def rsRIMKernelVector
    {F : Type} [Field F] {t k : ℕ}
    (p : Fin t → Polynomial F) (hp : ∀ j, (p j).degree < k)
    (root : Fin t) : RSRIMCol root k → F :=
  fun c => Polynomial.degreeLTEquiv F k
    ⟨p c.1.1 - p root, Polynomial.mem_degreeLT.mpr
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt (hp c.1.1) (hp root)))⟩ c.2

open scoped BigOperators in
theorem rsRIMKernelVector_eval_block
    {F : Type} [Field F] {t k : ℕ}
    (p : Fin t → Polynomial F) (hp : ∀ j, (p j).degree < k)
    (root j : Fin t) (hj : j ≠ root) (x : F) :
    (∑ d : Fin k, x ^ (d : ℕ) *
      rsRIMKernelVector p hp root
        (⟨⟨j, hj⟩, d⟩ : RSRIMCol root k)) =
      (p j).eval x - (p root).eval x := by
  have hq : p j - p root ∈ Polynomial.degreeLT F k :=
    Polynomial.mem_degreeLT.mpr
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt (hp j) (hp root)))
  rw [← Polynomial.eval_sub]
  rw [Polynomial.eval_eq_sum_degreeLTEquiv hq]
  apply Finset.sum_congr rfl
  intro d hd
  unfold rsRIMKernelVector
  rw [mul_comm]

open scoped BigOperators in
theorem rsRIMEval_mulVec_kernel_row
    {F : Type} [Field F] {t n k : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (α : Fin n → F)
    (p : Fin t → Polynomial F) (hp : ∀ j, (p j).degree < k)
    (r : RSRIMRow H) :
    Matrix.mulVec (rsRIMEval H root k α)
        (rsRIMKernelVector p hp root) r =
      (p r.1.2.1).eval (α r.1.1) -
        (p r.1.2.2).eval (α r.1.1) := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type]
  have hinner : ∀ c : {j : Fin t // j ≠ root},
      (∑ d : Fin k, rsRIMEval H root k α r (c, d) *
        rsRIMKernelVector p hp root (c, d)) =
        if c.1 = r.1.2.1 then
          (p c.1).eval (α r.1.1) - (p root).eval (α r.1.1)
        else if c.1 = r.1.2.2 then
          -((p c.1).eval (α r.1.1) - (p root).eval (α r.1.1))
        else 0 := by
    rintro ⟨j, hj⟩
    by_cases hja : j = r.1.2.1
    · subst j
      simp only [rsRIMEval, rsRIM, if_true, map_pow,
        MvPolynomial.eval_X]
      exact rsRIMKernelVector_eval_block p hp root r.1.2.1 hj
        (α r.1.1)
    · by_cases hjb : j = r.1.2.2
      · subst j
        have hba : r.1.2.2 ≠ r.1.2.1 :=
          (ne_of_lt r.2.2.2.1).symm
        simp only [rsRIMEval, rsRIM, hba, if_false, if_true,
          map_neg, map_pow, MvPolynomial.eval_X]
        calc
          (∑ d : Fin k, -(α r.1.1 ^ (d : ℕ)) *
              rsRIMKernelVector p hp root (⟨r.1.2.2, hj⟩, d)) =
              ∑ d : Fin k, -(α r.1.1 ^ (d : ℕ) *
                rsRIMKernelVector p hp root (⟨r.1.2.2, hj⟩, d)) := by
            apply Finset.sum_congr rfl
            intro d hd
            ring
          _ = -(∑ d : Fin k, α r.1.1 ^ (d : ℕ) *
                rsRIMKernelVector p hp root (⟨r.1.2.2, hj⟩, d)) := by
            rw [Finset.sum_neg_distrib]
          _ = -((p r.1.2.2).eval (α r.1.1) -
              (p root).eval (α r.1.1)) := by
            rw [rsRIMKernelVector_eval_block p hp root r.1.2.2 hj]
      · simp only [rsRIMEval, rsRIM, hja, hjb, if_false, map_zero,
          zero_mul, Finset.sum_const_zero]
  simp_rw [hinner]
  by_cases ha : r.1.2.1 = root
  · have hb : r.1.2.2 ≠ root := by
      intro hb
      exact (ne_of_lt r.2.2.2.1) (ha.trans hb.symm)
    let b : {j : Fin t // j ≠ root} := ⟨r.1.2.2, hb⟩
    have hnone : ∀ c : {j : Fin t // j ≠ root},
        ¬c.1 = r.1.2.1 := by
      intro c hc
      exact c.2 (hc.trans ha)
    simp only [hnone, if_false]
    have hbeq : ∀ c : {j : Fin t // j ≠ root},
        c.1 = r.1.2.2 ↔ c = b := by
      intro c
      constructor
      · intro hc
        exact Subtype.ext hc
      · intro hc
        exact congrArg Subtype.val hc
    simp_rw [hbeq]
    rw [Fintype.sum_ite_eq']
    dsimp only [b]
    rw [ha]
    ring
  · by_cases hb : r.1.2.2 = root
    · let a : {j : Fin t // j ≠ root} := ⟨r.1.2.1, ha⟩
      have hnone : ∀ c : {j : Fin t // j ≠ root},
          ¬c.1 = r.1.2.2 := by
        intro c hc
        exact c.2 (hc.trans hb)
      simp only [hnone, if_false]
      have haeq : ∀ c : {j : Fin t // j ≠ root},
          c.1 = r.1.2.1 ↔ c = a := by
        intro c
        constructor
        · intro hc
          exact Subtype.ext hc
        · intro hc
          exact congrArg Subtype.val hc
      simp_rw [haeq]
      rw [Fintype.sum_ite_eq']
      dsimp only [a]
      rw [hb]
    · let a : {j : Fin t // j ≠ root} := ⟨r.1.2.1, ha⟩
      let b : {j : Fin t // j ≠ root} := ⟨r.1.2.2, hb⟩
      have haeq : ∀ c : {j : Fin t // j ≠ root},
          c.1 = r.1.2.1 ↔ c = a := by
        intro c
        constructor
        · intro hc
          exact Subtype.ext hc
        · intro hc
          exact congrArg Subtype.val hc
      have hbeq : ∀ c : {j : Fin t // j ≠ root},
          c.1 = r.1.2.2 ↔ c = b := by
        intro c
        constructor
        · intro hc
          exact Subtype.ext hc
        · intro hc
          exact congrArg Subtype.val hc
      simp_rw [haeq, hbeq]
      have hab : a ≠ b := by
        intro hab
        exact (ne_of_lt r.2.2.2.1) (congrArg Subtype.val hab)
      have hba : b ≠ a := Ne.symm hab
      calc
        (∑ c : {j : Fin t // j ≠ root},
            if c = a then
              (p c.1).eval (α r.1.1) - (p root).eval (α r.1.1)
            else if c = b then
              -((p c.1).eval (α r.1.1) -
                (p root).eval (α r.1.1)) else 0) =
            (∑ c : {j : Fin t // j ≠ root},
              if c = a then
                (p c.1).eval (α r.1.1) - (p root).eval (α r.1.1)
              else 0) +
            (∑ c : {j : Fin t // j ≠ root},
              if c = b then
                -((p c.1).eval (α r.1.1) -
                  (p root).eval (α r.1.1)) else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro c hc
          by_cases hca : c = a
          · subst c
            simp only [if_true, hab, if_false, add_zero]
          · by_cases hcb : c = b
            · subst c
              simp only [hba, if_false, if_true, zero_add]
            · simp only [hca, hcb, if_false, add_zero]
        _ = ((p a.1).eval (α r.1.1) - (p root).eval (α r.1.1)) +
            -((p b.1).eval (α r.1.1) -
              (p root).eval (α r.1.1)) := by
          rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
        _ = (p r.1.2.1).eval (α r.1.1) -
            (p r.1.2.2).eval (α r.1.1) := by
          dsimp only [a, b]
          ring

theorem rsPatternWitness_rim_mulVec_kernel
    {F : Type} [Field F] {t n k : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (α : Fin n → F)
    (p : Fin t → Polynomial F) (hp : ∀ j, (p j).degree < k)
    (y : Fin n → F)
    (hagree : ∀ i j, j ∈ H i → (p j).eval (α i) = y i) :
    Matrix.mulVec (rsRIMEval H root k α)
      (rsRIMKernelVector p hp root) = 0 := by
  funext r
  rw [rsRIMEval_mulVec_kernel_row]
  have ha := hagree r.1.1 r.1.2.1 r.2.1
  have hb := hagree r.1.1 r.1.2.2 r.2.2.1
  simp only [ha, hb, sub_self, Pi.zero_apply]

theorem rsRIMKernelVector_ne_zero
    {F : Type} [Field F] {t k : ℕ}
    (p : Fin t → Polynomial F) (hp : ∀ j, (p j).degree < k)
    (hinj : Function.Injective p) (root : Fin t) (ht : 2 ≤ t) :
    rsRIMKernelVector p hp root ≠ 0 := by
  have ht' : 1 < Fintype.card (Fin t) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card ht' root
  let q : Polynomial.degreeLT F k :=
    ⟨p j - p root, Polynomial.mem_degreeLT.mpr
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt (hp j) (hp root)))⟩
  intro hv
  have hqmap : Polynomial.degreeLTEquiv F k q = 0 := by
    funext d
    have hd := congrFun hv
      (⟨⟨j, hj⟩, d⟩ : RSRIMCol root k)
    change (Polynomial.degreeLTEquiv F k q) d = 0
    simpa only [rsRIMKernelVector, q, Pi.zero_apply] using hd
  have hqzero : q = 0 :=
    (Polynomial.degreeLTEquiv F k).injective hqmap
  have hsub : p j - p root = 0 := by
    exact congrArg Subtype.val hqzero
  exact hj (hinj (sub_eq_zero.mp hsub))

noncomputable def rsRIMMinor {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (k : ℕ)
    (ρ : RSRIMCol root k ↪ RSRIMRow H) :
    Matrix (RSRIMCol root k) (RSRIMCol root k) (MvPolynomial (Fin n) F) :=
  fun a b => rsRIM H root k (ρ a) b

theorem rsPatternErase_rimMinor_eq
    {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (B : Finset (Fin n))
    (root : Fin t) (k : ℕ)
    (ρ : RSRIMCol root k ↪ RSRIMRow (rsPatternEraseCoordinates H B)) :
    rsRIMMinor (F := F) H root k
        (ρ.trans (rsPatternErase_rimRowEmbedding H B)) =
      rsRIMMinor (F := F) (rsPatternEraseCoordinates H B) root k ρ := by
  funext a b
  exact rsPatternErase_rim_entry (F := F) H B root k (ρ a) b

noncomputable def rsRIMHasFullColumnRank {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (k : ℕ) : Prop :=
  ∃ ρ : RSRIMCol root k ↪ RSRIMRow H,
    Matrix.det (rsRIMMinor (F := F) H root k ρ) ≠ 0

theorem rsPatternErase_fullRankMinor_avoiding
    {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (B : Finset (Fin n))
    (root : Fin t) (k : ℕ)
    (hfull : rsRIMHasFullColumnRank (F := F)
      (rsPatternEraseCoordinates H B) root k) :
    ∃ ρ : RSRIMCol root k ↪ RSRIMRow H,
      (∀ c, (ρ c).1.1 ∉ B) ∧
        Matrix.det (rsRIMMinor (F := F) H root k ρ) ≠ 0 := by
  rcases hfull with ⟨ρ, hρ⟩
  refine ⟨ρ.trans (rsPatternErase_rimRowEmbedding H B), ?_, ?_⟩
  · intro c
    exact rsPatternErase_rimRowEmbedding_coord_notMem H B (ρ c)
  · rw [rsPatternErase_rimMinor_eq]
    exact hρ

theorem rsPatternFillEmpty_rimHasFullColumnRank
    {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (fallback root : Fin t) (k : ℕ)
    (hfull : rsRIMHasFullColumnRank (F := F)
      (rsPatternFillEmpty H fallback) root k) :
    rsRIMHasFullColumnRank (F := F) H root k := by
  rcases hfull with ⟨ρ, hρ⟩
  let ρ' : RSRIMCol root k ↪ RSRIMRow H :=
    ρ.trans (rsPatternFillEmpty_rimRowEquiv H fallback).toEmbedding
  refine ⟨ρ', ?_⟩
  have hminor : rsRIMMinor (F := F) H root k ρ' =
      rsRIMMinor (F := F) (rsPatternFillEmpty H fallback) root k ρ := by
    funext a b
    exact rsPatternFillEmpty_rim_entry (F := F)
      H fallback root k (ρ a) b
  rw [hminor]
  exact hρ

noncomputable def rsRIMMinorEval {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (k : ℕ)
    (α : Fin n → F) (ρ : RSRIMCol root k ↪ RSRIMRow H) :
    Matrix (RSRIMCol root k) (RSRIMCol root k) F :=
  fun a b => MvPolynomial.eval α (rsRIMMinor (F := F) H root k ρ a b)

@[simp] theorem rsRIMMinorEval_apply {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (k : ℕ)
    (α : Fin n → F) (ρ : RSRIMCol root k ↪ RSRIMRow H)
    (a b : RSRIMCol root k) :
    rsRIMMinorEval H root k α ρ a b =
      rsRIMEval H root k α (ρ a) b := rfl

theorem rsRIMMinorEval_det
    {F : Type} [Field F] {t n : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (k : ℕ)
    (α : Fin n → F) (ρ : RSRIMCol root k ↪ RSRIMRow H) :
    MvPolynomial.eval α
        (Matrix.det (rsRIMMinor (F := F) H root k ρ)) =
      Matrix.det (rsRIMMinorEval H root k α ρ) := by
  rw [RingHom.map_det]
  rfl

open scoped BigOperators in
theorem rsRIMMinorEval_mulVec_kernel
    {F : Type} [Field F] {t n k : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t) (α : Fin n → F)
    (ρ : RSRIMCol root k ↪ RSRIMRow H) (v : RSRIMCol root k → F)
    (hker : Matrix.mulVec (rsRIMEval H root k α) v = 0) :
    Matrix.mulVec (rsRIMMinorEval H root k α ρ) v = 0 := by
  funext a
  have ha := congrFun hker (ρ a)
  simpa only [Matrix.mulVec, dotProduct, rsRIMMinorEval_apply,
    Pi.zero_apply] using ha

theorem rsPatternOccurs_imp_rim_minor_det_eval_zero
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {t n k : ℕ} (H : RSAgreementPattern t n) (α : Fin n ↪ F)
    (hocc : rsPatternOccurs t n k H α) (ht : 2 ≤ t)
    (root : Fin t) (ρ : RSRIMCol root k ↪ RSRIMRow H) :
    MvPolynomial.eval (α : Fin n → F)
      (Matrix.det (rsRIMMinor (F := F) H root k ρ)) = 0 := by
  rcases hocc with ⟨p, hp_inj, hp_deg, y, hy⟩
  have hwhole : Matrix.mulVec
      (rsRIMEval H root k (α : Fin n → F))
      (rsRIMKernelVector p hp_deg root) = 0 :=
    rsPatternWitness_rim_mulVec_kernel H root (α : Fin n → F)
      p hp_deg y (fun i j hj => (hy i j).mp hj)
  have hminor : Matrix.mulVec
      (rsRIMMinorEval H root k (α : Fin n → F) ρ)
      (rsRIMKernelVector p hp_deg root) = 0 :=
    rsRIMMinorEval_mulVec_kernel H root (α : Fin n → F) ρ
      (rsRIMKernelVector p hp_deg root) hwhole
  have hv : rsRIMKernelVector p hp_deg root ≠ 0 :=
    rsRIMKernelVector_ne_zero p hp_deg hp_inj root ht
  have hdet : Matrix.det
      (rsRIMMinorEval H root k (α : Fin n → F) ρ) = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hv, hminor⟩
  rw [rsRIMMinorEval_det]
  exact hdet

noncomputable def rsRandomRadius (ℓ k n : ℕ) (η : ℝ) : ℝ :=
  (ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η)

structure RSBadPolynomialWitness {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (α : Fin n ↪ F) where
  p : Fin (ℓ + 1) → Polynomial F
  p_injective : Function.Injective p
  degree_lt : ∀ j, (p j).degree < k
  y : Fin n → F
  distance_le : ∀ j,
    ((hammingDist y (fun i => (p j).eval (α i)) : ℕ) : ℝ) / (n : ℝ) ≤
      rsRandomRadius ℓ k n η

def rsBadPolynomialFamilyDomain
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (S : {S : Finset F // S.card = n}) : Prop :=
  ∃ f : ↥(S : Finset F) → F,
    ∃ P : Finset (Polynomial F),
      P.card = ℓ + 1 ∧
        (∀ p ∈ P, p.degree < k) ∧
        ∀ p ∈ P, ReedSolomon.evalOnPoints
          (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) p ∈
            Code.relHammingBall f (rsRandomRadius ℓ k n η)

noncomputable def rsBadPolynomialFamilyDomains
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) : Finset {S : Finset F // S.card = n} := by
  classical
  exact Finset.univ.filter (rsBadPolynomialFamilyDomain ℓ k n η)

noncomputable def rsBadPolynomialWitnessPattern
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} {α : Fin n ↪ F}
    (W : RSBadPolynomialWitness ℓ k n η α) :
    RSAgreementPattern (ℓ + 1) n :=
  fun i => Finset.univ.filter fun j => (W.p j).eval (α i) = W.y i

theorem rsBadPolynomialWitness_agreement_card_lower
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} {α : Fin n ↪ F}
    (W : RSBadPolynomialWitness ℓ k n η α) (hn_pos : 0 < n)
    (j : Fin (ℓ + 1)) :
    (n : ℝ) * (1 - rsRandomRadius ℓ k n η) ≤
      ((Finset.univ.filter fun i : Fin n =>
        (W.p j).eval (α i) = W.y i).card : ℝ) := by
  let v : Fin n → F := fun i => (W.p j).eval (α i)
  have hlow := agreement_lower_of_normalized_distance_le n
    (hammingDist W.y v) (rsRandomRadius ℓ k n η) hn_pos (by
      simpa only [v] using W.distance_le j)
  have hdle : hammingDist W.y v ≤ n := by
    simpa only [Fintype.card_fin] using
      (hammingDist_le_card_fintype (x := W.y) (y := v))
  have hcard := card_agreement_eq_card_sub_hammingDist W.y v
  have hcast :
      ((Finset.univ.filter fun i : Fin n => W.y i = v i).card : ℝ) =
        (n : ℝ) - (hammingDist W.y v : ℝ) := by
    rw [hcard, Fintype.card_fin, Nat.cast_sub hdle]
  have hfilter :
      (Finset.univ.filter fun i : Fin n => v i = W.y i) =
        Finset.univ.filter fun i : Fin n => W.y i = v i := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact eq_comm
  calc
    (n : ℝ) * (1 - rsRandomRadius ℓ k n η) ≤
        (n : ℝ) - (hammingDist W.y v : ℝ) := hlow
    _ = ((Finset.univ.filter fun i : Fin n => W.y i = v i).card : ℝ) :=
      hcast.symm
    _ = ((Finset.univ.filter fun i : Fin n => v i = W.y i).card : ℝ) := by
      rw [hfilter]
    _ = ((Finset.univ.filter fun i : Fin n =>
        (W.p j).eval (α i) = W.y i).card : ℝ) := by
      rfl

theorem rsBadPolynomialWitness_pattern_occurs
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} {α : Fin n ↪ F}
    (W : RSBadPolynomialWitness ℓ k n η α) :
    rsPatternOccurs (ℓ + 1) n k (rsBadPolynomialWitnessPattern W) α := by
  refine ⟨W.p, W.p_injective, W.degree_lt, W.y, ?_⟩
  intro i j
  unfold rsBadPolynomialWitnessPattern
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def rsBadSubsetOrders
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) :
    Finset ({S : Finset F // S.card = n} × Equiv.Perm (Fin n)) :=
  (rsBadPolynomialFamilyDomains (F := F) ℓ k n η).product Finset.univ

noncomputable def rsDomainBadList {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (S : {S : Finset F // S.card = n}) : Prop :=
  ∃ (y : ↥(S : Finset F) → F) (T : Finset (↥(S : Finset F) → F)),
    T.card = ℓ + 1 ∧
      ∀ c ∈ T, c ∈ closeCodewordsRel
        ((ReedSolomon.code
          (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) k :
            Set (↥(S : Finset F) → F))) y (rsRandomRadius ℓ k n η)

theorem rsDomainBadList_imp_badPolynomialFamilyDomain
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} (S : {S : Finset F // S.card = n})
    (hbad : rsDomainBadList ℓ k n η S) :
    rsBadPolynomialFamilyDomain ℓ k n η S := by
  classical
  rcases hbad with ⟨f, T, hTcard, hT⟩
  let e : Fin (ℓ + 1) ≃ ↥T :=
    (Finset.equivFinOfCardEq hTcard).symm
  have hex : ∀ j : Fin (ℓ + 1),
      ∃ p : Polynomial F, p.degree < k ∧
        ∀ x, p.eval
          (Function.Embedding.subtype
            (fun z : F => z ∈ (S : Finset F)) x) = (e j : ↥T).1 x := by
    intro j
    have hclose := hT (e j) (e j).property
    simp only [closeCodewordsRel, Set.mem_setOf_eq] at hclose
    exact ReedSolomon.mem_code_iff_eval.mp hclose.1
  let p : Fin (ℓ + 1) → Polynomial F := fun j => Classical.choose (hex j)
  have hpdeg : ∀ j, (p j).degree < k := by
    intro j
    exact (Classical.choose_spec (hex j)).1
  have hpeval : ∀ j x,
      (p j).eval
        (Function.Embedding.subtype
          (fun z : F => z ∈ (S : Finset F)) x) = (e j : ↥T).1 x := by
    intro j x
    exact (Classical.choose_spec (hex j)).2 x
  have hpinj : Function.Injective p := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    funext x
    calc
      (e a : ↥T).1 x = (p a).eval
          (Function.Embedding.subtype
            (fun z : F => z ∈ (S : Finset F)) x) := (hpeval a x).symm
      _ = (p b).eval
          (Function.Embedding.subtype
            (fun z : F => z ∈ (S : Finset F)) x) := by rw [hab]
      _ = (e b : ↥T).1 x := hpeval b x
  let pe : Fin (ℓ + 1) ↪ Polynomial F := ⟨p, hpinj⟩
  let P : Finset (Polynomial F) := Finset.univ.map pe
  refine ⟨f, P, ?_, ?_, ?_⟩
  · dsimp only [P]
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro q hq
    dsimp only [P] at hq
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hq
    exact hpdeg j
  · intro q hq
    dsimp only [P] at hq
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_map.mp hq
    have hclose := hT (e j) (e j).property
    simp only [closeCodewordsRel, Set.mem_setOf_eq] at hclose
    have hdec :
        (fun a b : F => Classical.propDecidable (a = b)) =
          (inferInstance : DecidableEq F) := Subsingleton.elim _ _
    rw [hdec] at hclose
    change ReedSolomon.evalOnPoints
        (Function.Embedding.subtype
          (fun z : F => z ∈ (S : Finset F))) (p j) ∈
      Code.relHammingBall f (rsRandomRadius ℓ k n η)
    have hword : ReedSolomon.evalOnPoints
        (Function.Embedding.subtype
          (fun z : F => z ∈ (S : Finset F))) (p j) = (e j : ↥T).1 := by
      funext x
      exact hpeval j x
    rw [hword]
    exact hclose.2

noncomputable def rsDomainGood {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (S : {S : Finset F // S.card = n}) : Prop :=
  Lambda ((ReedSolomon.code
      (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) k :
    Set (↥(S : Finset F) → F))) (rsRandomRadius ℓ k n η) ≤ (ℓ : ℕ∞)

theorem rsDomainBadList_of_not_good
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (S : {S : Finset F // S.card = n})
    (hnot : ¬rsDomainGood ℓ k n η S) :
    rsDomainBadList ℓ k n η S := by
  unfold rsDomainGood at hnot
  unfold rsDomainBadList
  by_contra hbad
  apply hnot
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  by_contra hcard
  have hsize : ℓ + 1 ≤ T.card := by omega
  obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq hsize
  apply hbad
  exact ⟨y, U, hUcard, fun c hc => hT c (hUT hc)⟩

theorem rsDomainGood_no_badList
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (S : {S : Finset F // S.card = n})
    (hgood : rsDomainGood ℓ k n η S) :
    ¬rsDomainBadList ℓ k n η S := by
  intro hbad
  rcases hbad with ⟨y, T, hTcard, hT⟩
  unfold rsDomainGood at hgood
  have hpoint := (Lambda_le_iff_forall_encard_le.mp hgood) y
  have hsubset : (T : Set (↥(S : Finset F) → F)) ⊆
      closeCodewordsRel
        ((ReedSolomon.code
          (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) k :
            Set (↥(S : Finset F) → F))) y (rsRandomRadius ℓ k n η) := by
    intro c hc
    exact hT c hc
  have henc := (Set.encard_mono hsubset).trans hpoint
  rw [Set.encard_coe_eq_coe_finsetCard] at henc
  have hcard_le : T.card ≤ ℓ := by exact_mod_cast henc
  omega

theorem rsDomainGood_iff_no_badList
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (S : {S : Finset F // S.card = n}) :
    rsDomainGood ℓ k n η S ↔ ¬rsDomainBadList ℓ k n η S := by
  constructor
  · exact rsDomainGood_no_badList ℓ k n η S
  · intro hno
    by_contra hnot
    exact hno (rsDomainBadList_of_not_good ℓ k n η S hnot)

theorem rsDomainGood_of_k_eq_zero
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (S : {S : Finset F // S.card = n})
    (hℓ : 1 ≤ ℓ) (hk : k = 0) :
    rsDomainGood ℓ k n η S := by
  subst k
  unfold rsDomainGood
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  apply (Finset.card_le_one.mpr ?_).trans hℓ
  intro a ha b hb
  have hca := hT a ha
  have hcb := hT b hb
  simp only [closeCodewordsRel, Set.mem_setOf_eq] at hca hcb
  have hmem_a : a ∈ ReedSolomon.code
      (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) 0 := hca.1
  have hmem_b : b ∈ ReedSolomon.code
      (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) 0 := hcb.1
  rw [ReedSolomon.code_zero] at hmem_a hmem_b
  have ha0 : a = 0 := (Submodule.mem_bot F).mp hmem_a
  have hb0 : b = 0 := (Submodule.mem_bot F).mp hmem_b
  exact ha0.trans hb0.symm

theorem rsDomainGood_of_radius_neg
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) (S : {S : Finset F // S.card = n})
    (hn_pos : 0 < n) (hr : rsRandomRadius ℓ k n η < 0) :
    rsDomainGood ℓ k n η S := by
  have hScard : 0 < (S : Finset F).card := by
    simpa only [S.property] using hn_pos
  letI : Nonempty ↥(S : Finset F) := (Finset.card_pos.mp hScard).to_subtype
  unfold rsDomainGood
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  have hnone : ¬T.Nonempty := by
    rintro ⟨c, hc⟩
    have hclose := hT c hc
    simp only [closeCodewordsRel, Set.mem_setOf_eq] at hclose
    have hball := hclose.2
    simp only [Code.relHammingBall, Set.mem_setOf_eq] at hball
    have hdec :
        (fun a b : F => Classical.propDecidable (a = b)) =
          (inferInstance : DecidableEq F) := Subsingleton.elim _ _
    rw [hdec] at hball
    have hnonneg : (0 : ℝ) ≤ (Code.relHammingDist y c : ℝ) := by
      exact_mod_cast Code.zero_le_relHammingDist
    exact (not_lt_of_ge hnonneg) (lt_of_le_of_lt hball hr)
  have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  simp only [hTempty, Finset.card_empty, Nat.zero_le]

theorem rsRandomRadius_agreement_identity
    (ℓ k n : ℕ) (η : ℝ) (hn : 0 < n) :
    ((ℓ : ℝ) + 1) * (n : ℝ) *
        (1 - rsRandomRadius ℓ k n η) - (n : ℝ) =
      (ℓ : ℝ) * ((k : ℝ) + η * (n : ℝ)) := by
  unfold rsRandomRadius
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hℓ0 : (ℓ : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn0, hℓ0]
  ring

noncomputable def rsRootDemand {t : ℕ}
    (root : Fin t) (k : ℕ) (U : Finset (Fin t)) : ℕ :=
  if root ∈ U ∧ U ≠ (Finset.univ : Finset (Fin t)) then k else 0

theorem rsRootDemand_crossingSupermodular {t k : ℕ} (root : Fin t) :
    rsCrossingSupermodular (rsRootDemand root k) := by
  classical
  unfold rsCrossingSupermodular
  intro U V hcross
  have hUne : U ≠ (Finset.univ : Finset (Fin t)) := by
    intro hU
    rcases hcross.2.2.1 with ⟨x, hx⟩
    have hxnot := (Finset.mem_sdiff.mp hx).2
    apply hxnot
    rw [hU]
    exact Finset.mem_univ x
  have hVne : V ≠ (Finset.univ : Finset (Fin t)) := by
    intro hV
    rcases hcross.2.1 with ⟨x, hx⟩
    have hxnot := (Finset.mem_sdiff.mp hx).2
    apply hxnot
    rw [hV]
    exact Finset.mem_univ x
  have hIne : U ∩ V ≠ (Finset.univ : Finset (Fin t)) := by
    intro hI
    apply hUne
    apply Finset.eq_univ_of_forall
    intro x
    have hx : x ∈ U ∩ V := by
      rw [hI]
      exact Finset.mem_univ x
    exact (Finset.mem_inter.mp hx).1
  have hUnionNe : U ∪ V ≠ (Finset.univ : Finset (Fin t)) := by
    intro hUnion
    rcases hcross.2.2.2 with ⟨x, hx⟩
    have hxnot := (Finset.mem_sdiff.mp hx).2
    apply hxnot
    rw [hUnion]
    exact Finset.mem_univ x
  by_cases hu : root ∈ U
  · by_cases hv : root ∈ V
    · simp [rsRootDemand, hu, hv, hUne, hVne, hIne, hUnionNe]
    · simp [rsRootDemand, hu, hv, hUne, hVne, hIne, hUnionNe]
  · by_cases hv : root ∈ V
    · simp [rsRootDemand, hu, hv, hUne, hVne, hIne, hUnionNe]
    · simp [rsRootDemand, hu, hv, hUne, hVne, hIne, hUnionNe]

theorem rsRootedCutOrientation_root_indegree_ge
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t) :
    k ≤ rsOrientationIndegree H R.orientation R.edge_nonempty R.root := by
  classical
  let K : Finset (Fin t) := Finset.univ.erase R.root
  have htcard : 1 < Fintype.card (Fin t) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨v, hv⟩ := Fintype.exists_ne_of_one_lt_card htcard R.root
  have hKne : K.Nonempty := by
    refine ⟨v, ?_⟩
    simp only [K, Finset.mem_erase, Finset.mem_univ, and_true]
    exact hv
  have hroot : R.root ∉ K := by
    simp only [K, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      not_false_eq_true]
  have hcut := R.cut_bound K hKne hroot
  apply hcut.trans
  apply Finset.card_le_card
  intro i hi
  simp only [rsOrientationExitEdges, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi
  change i ∈ Finset.univ.filter
    (fun j => R.orientation.head j (R.edge_nonempty j) = R.root)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ i, ?_⟩
  simpa only [K, Finset.mem_erase, Finset.mem_univ, and_true, not_not]
    using hi.1

noncomputable def rsRootedMultiplicity {t n k : ℕ}
    {H : RSAgreementPattern t n} (R : RSRootedCutOrientation H k)
    (v : Fin t) : ℕ :=
  if v = R.root then
    rsOrientationIndegree H R.orientation R.edge_nonempty v - k
  else rsOrientationIndegree H R.orientation R.edge_nonempty v

abbrev RSRootedGZPIndex {t n k : ℕ}
    {H : RSAgreementPattern t n} (R : RSRootedCutOrientation H k) :=
  Σ v : Fin t, Fin (rsRootedMultiplicity R v)

noncomputable def rsRootedGZPSupport
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k)
    (K : Finset (RSRootedGZPIndex R)) : Finset (Fin t) :=
  K.image fun a => a.1

open scoped BigOperators in
theorem rsRootedGZPIndex_card_le_sum_support_multiplicity
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k)
    (K : Finset (RSRootedGZPIndex R)) :
    K.card ≤ ∑ v ∈ rsRootedGZPSupport R K,
      rsRootedMultiplicity R v := by
  classical
  have hsub : K ⊆
      (rsRootedGZPSupport R K).sigma (fun v =>
        (Finset.univ : Finset (Fin (rsRootedMultiplicity R v)))) := by
    intro a ha
    rw [Finset.mem_sigma]
    refine ⟨?_, Finset.mem_univ a.2⟩
    rw [rsRootedGZPSupport]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  calc
    K.card ≤ ((rsRootedGZPSupport R K).sigma (fun v =>
        (Finset.univ : Finset
          (Fin (rsRootedMultiplicity R v))))).card :=
      Finset.card_le_card hsub
    _ = ∑ v ∈ rsRootedGZPSupport R K,
          (Finset.univ : Finset
            (Fin (rsRootedMultiplicity R v))).card := by
      rw [Finset.card_sigma]
    _ = ∑ v ∈ rsRootedGZPSupport R K,
          rsRootedMultiplicity R v := by
      simp only [Finset.card_univ, Fintype.card_fin]

theorem rsRootedGZPSupport_nonempty
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (K : Finset (RSRootedGZPIndex R))
    (hK : K.Nonempty) : (rsRootedGZPSupport R K).Nonempty := by
  rcases hK with ⟨a, ha⟩
  refine ⟨a.1, ?_⟩
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

theorem rsRootedMultiplicity_add_root_correction
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t) (v : Fin t) :
    rsRootedMultiplicity R v + (if v = R.root then k else 0) =
      rsOrientationIndegree H R.orientation R.edge_nonempty v := by
  classical
  have hroot :
      k ≤ rsOrientationIndegree H R.orientation R.edge_nonempty R.root :=
    rsRootedCutOrientation_root_indegree_ge R ht
  by_cases hv : v = R.root
  · subst v
    simp only [rsRootedMultiplicity, if_pos, Nat.sub_add_cancel hroot]
  · simp only [rsRootedMultiplicity, hv, if_false, add_zero]

open scoped BigOperators in
theorem rsRootedMultiplicity_sum
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t) :
    ∑ v : Fin t, rsRootedMultiplicity R v = n - k := by
  classical
  have hroot :
      k ≤ rsOrientationIndegree H R.orientation R.edge_nonempty R.root :=
    rsRootedCutOrientation_root_indegree_ge R ht
  have hpoint : ∀ v : Fin t,
      rsRootedMultiplicity R v + (if v = R.root then k else 0) =
        rsOrientationIndegree H R.orientation R.edge_nonempty v := by
    intro v
    by_cases hv : v = R.root
    · subst v
      simp only [rsRootedMultiplicity, if_pos, Nat.sub_add_cancel hroot]
    · simp only [rsRootedMultiplicity, hv, if_false, add_zero]
  have hsum :
      (∑ v : Fin t,
        (rsRootedMultiplicity R v + (if v = R.root then k else 0))) = n := by
    calc
      (∑ v : Fin t,
          (rsRootedMultiplicity R v + (if v = R.root then k else 0))) =
          ∑ v : Fin t,
            rsOrientationIndegree H R.orientation R.edge_nonempty v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hpoint v
      _ = n := rsOrientationIndegree_sum H R.orientation R.edge_nonempty
  rw [Finset.sum_add_distrib, Fintype.sum_ite_eq'] at hsum
  omega

open scoped BigOperators in
theorem rsRootedGZPIndex_card
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t) :
    Fintype.card (RSRootedGZPIndex R) = n - k := by
  rw [Fintype.card_sigma]
  simp only [RSRootedGZPIndex, Fintype.card_fin]
  exact rsRootedMultiplicity_sum R ht

open scoped BigOperators in
theorem rsRootedMultiplicity_sum_with_root_correction
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t)
    (U : Finset (Fin t)) :
    (∑ v ∈ U,
      (rsRootedMultiplicity R v + (if v = R.root then k else 0))) =
      ∑ v ∈ U,
        rsOrientationIndegree H R.orientation R.edge_nonempty v := by
  classical
  apply Finset.sum_congr rfl
  intro v hv
  exact rsRootedMultiplicity_add_root_correction R ht v

open scoped BigOperators in
theorem rsRootedMultiplicity_sum_on_of_root_mem
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t)
    (U : Finset (Fin t)) (hroot : R.root ∈ U) :
    (∑ v ∈ U, rsRootedMultiplicity R v) + k =
      ∑ v ∈ U,
        rsOrientationIndegree H R.orientation R.edge_nonempty v := by
  classical
  have h := rsRootedMultiplicity_sum_with_root_correction R ht U
  rw [Finset.sum_add_distrib] at h
  have hcorr : (∑ v ∈ U, if v = R.root then k else 0) = k := by
    simpa only using
      (Finset.sum_ite_eq_of_mem' U R.root (fun _ => k) hroot)
  rw [hcorr] at h
  exact h

open scoped BigOperators in
theorem rsRootedMultiplicity_sum_on_of_root_not_mem
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t)
    (U : Finset (Fin t)) (hroot : R.root ∉ U) :
    (∑ v ∈ U, rsRootedMultiplicity R v) =
      ∑ v ∈ U,
        rsOrientationIndegree H R.orientation R.edge_nonempty v := by
  classical
  have h := rsRootedMultiplicity_sum_with_root_correction R ht U
  rw [Finset.sum_add_distrib] at h
  have hcorr : (∑ v ∈ U, if v = R.root then k else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [if_neg]
    intro hvr
    apply hroot
    rw [← hvr]
    exact hv
  rw [hcorr, add_zero] at h
  exact h

open scoped BigOperators in
theorem rsRootedGZP_internalEdges_le_sum_compl_multiplicity
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t)
    (J : Finset (Fin t)) (hJ : J.Nonempty) :
    (rsPatternInternalEdges H
      ((Finset.univ : Finset (Fin t)) \ J)).card ≤
      ∑ v ∈ (Finset.univ : Finset (Fin t)) \ J,
        rsRootedMultiplicity R v := by
  classical
  let U : Finset (Fin t) := (Finset.univ : Finset (Fin t)) \ J
  change (rsPatternInternalEdges H U).card ≤
    ∑ v ∈ U, rsRootedMultiplicity R v
  by_cases hroot : R.root ∈ U
  · have hrootJ : R.root ∉ J := by
      intro hrJ
      have hrU : R.root ∈
          (Finset.univ : Finset (Fin t)) \ J := by
        simpa only [U] using hroot
      exact (Finset.mem_sdiff.mp hrU).2 hrJ
    have hcut := R.cut_bound J hJ hrootJ
    have hIntSub : rsPatternInternalEdges H U ⊆
        rsOrientationHeadInEdges H R.orientation R.edge_nonempty U :=
      rsPatternInternalEdges_subset_headInEdges
        H R.orientation R.edge_nonempty U
    have hExitSub : rsOrientationExitEdges H R.orientation
        R.edge_nonempty J ⊆
        rsOrientationHeadInEdges H R.orientation R.edge_nonempty U := by
      simpa only [U] using
        (rsOrientationExitEdges_subset_headIn_compl
          H R.orientation R.edge_nonempty J)
    have hdis : Disjoint (rsPatternInternalEdges H U)
        (rsOrientationExitEdges H R.orientation R.edge_nonempty J) := by
      simpa only [U] using
        (rsPatternInternalEdges_disjoint_exitEdges
          H R.orientation R.edge_nonempty J)
    have hcard := Finset.card_le_card (Finset.union_subset hIntSub hExitSub)
    rw [Finset.card_union_of_disjoint hdis,
      rsOrientationHeadInEdges_card] at hcard
    have hsum := rsRootedMultiplicity_sum_on_of_root_mem R ht U hroot
    omega
  · calc
      (rsPatternInternalEdges H U).card ≤
          (rsOrientationHeadInEdges H R.orientation
            R.edge_nonempty U).card :=
        Finset.card_le_card
          (rsPatternInternalEdges_subset_headInEdges
            H R.orientation R.edge_nonempty U)
      _ = ∑ v ∈ U,
          rsOrientationIndegree H R.orientation R.edge_nonempty v :=
        rsOrientationHeadInEdges_card
          H R.orientation R.edge_nonempty U
      _ = ∑ v ∈ U, rsRootedMultiplicity R v :=
        (rsRootedMultiplicity_sum_on_of_root_not_mem
          R ht U hroot).symm

noncomputable def rsSubsetIndexEquiv {F : Type} [DecidableEq F] {n : ℕ}
    (S : {S : Finset F // S.card = n}) :
    Fin n ≃ ↥(S : Finset F) :=
  (Finset.equivFinOfCardEq S.property).symm

noncomputable def rsSubsetEmbedding {F : Type} [DecidableEq F] {n : ℕ}
    (S : {S : Finset F // S.card = n}) : Fin n ↪ F :=
  (rsSubsetIndexEquiv S).toEmbedding.trans
    (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F)))

@[simp] theorem rsSubsetEmbedding_apply {F : Type} [DecidableEq F] {n : ℕ}
    (S : {S : Finset F // S.card = n}) (i : Fin n) :
    rsSubsetEmbedding S i = (rsSubsetIndexEquiv S i : F) := rfl

theorem rsBadPolynomialFamilyDomain_exists_badPolynomialWitness
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} (S : {S : Finset F // S.card = n})
    (hbad : rsBadPolynomialFamilyDomain ℓ k n η S) :
    Nonempty (RSBadPolynomialWitness ℓ k n η (rsSubsetEmbedding S)) := by
  classical
  rcases hbad with ⟨f, P, hPcard, hPdeg, hPball⟩
  let e : Fin (ℓ + 1) ≃ ↥P :=
    (Finset.equivFinOfCardEq hPcard).symm
  let p : Fin (ℓ + 1) → Polynomial F := fun j => (e j : Polynomial F)
  refine ⟨{
    p := p
    p_injective := ?_
    degree_lt := ?_
    y := f ∘ rsSubsetIndexEquiv S
    distance_le := ?_ }⟩
  · intro a b hab
    apply e.injective
    exact Subtype.ext hab
  · intro j
    exact hPdeg (e j) (e j).property
  · intro j
    have hball := hPball (e j) (e j).property
    simp only [Code.relHammingBall, Set.mem_setOf_eq] at hball
    let w : ↥(S : Finset F) → F :=
      ReedSolomon.evalOnPoints
        (Function.Embedding.subtype
          (fun z : F => z ∈ (S : Finset F))) (e j)
    have hball' :
        ((hammingDist f w : ℕ) : ℝ) / (n : ℝ) ≤
          rsRandomRadius ℓ k n η := by
      simpa only [Code.relHammingDist, NNRat.cast_div,
        NNRat.cast_natCast, Fintype.card_coe, S.property] using hball
    have hevalfun :
        (fun i : Fin n => (p j).eval (rsSubsetEmbedding S i)) =
          w ∘ rsSubsetIndexEquiv S := by
      funext i
      rw [rsSubsetEmbedding_apply]
      rfl
    rw [hevalfun]
    rw [hammingDist_precomp_equiv (rsSubsetIndexEquiv S)]
    exact hball'

noncomputable def rsDomainBadList_to_badPolynomialWitness
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} (S : {S : Finset F // S.card = n})
    (hn_pos : 0 < n) (hbad : rsDomainBadList ℓ k n η S) :
    RSBadPolynomialWitness ℓ k n η (rsSubsetEmbedding S) := by
  classical
  have hScard : 0 < (S : Finset F).card := by
    simpa only [S.property] using hn_pos
  letI : Nonempty ↥(S : Finset F) :=
    (Finset.card_pos.mp hScard).to_subtype
  unfold rsDomainBadList at hbad
  let y : ↥(S : Finset F) → F := Classical.choose hbad
  have hy := Classical.choose_spec hbad
  let T : Finset (↥(S : Finset F) → F) := Classical.choose hy
  have hTspec := Classical.choose_spec hy
  have hTcard : T.card = ℓ + 1 := hTspec.1
  have hT : ∀ c ∈ T, c ∈ closeCodewordsRel
      ((ReedSolomon.code
        (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) k :
          Set (↥(S : Finset F) → F))) y (rsRandomRadius ℓ k n η) := hTspec.2
  let e : Fin (ℓ + 1) ≃ ↥T :=
    (Finset.equivFinOfCardEq hTcard).symm
  have hcode : ∀ j : Fin (ℓ + 1),
      (e j : ↥(S : Finset F) → F) ∈ ReedSolomon.code
        (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) k := by
    intro j
    have hclose := hT (e j) (e j).property
    exact hclose.1
  have hex : ∀ j : Fin (ℓ + 1),
      ∃ p : Polynomial F, p.degree < k ∧
        ∀ x, p.eval
          (Function.Embedding.subtype
            (fun z : F => z ∈ (S : Finset F)) x) = (e j : ↥T).1 x := by
    intro j
    exact ReedSolomon.mem_code_iff_eval.mp (hcode j)
  let p : Fin (ℓ + 1) → Polynomial F := fun j => Classical.choose (hex j)
  have hpdeg : ∀ j, (p j).degree < k := by
    intro j
    exact (Classical.choose_spec (hex j)).1
  have hpeval : ∀ j x,
      (p j).eval
        (Function.Embedding.subtype
          (fun z : F => z ∈ (S : Finset F)) x) = (e j : ↥T).1 x := by
    intro j x
    exact (Classical.choose_spec (hex j)).2 x
  refine
    { p := p
      p_injective := ?_
      degree_lt := hpdeg
      y := y ∘ rsSubsetIndexEquiv S
      distance_le := ?_ }
  · intro a b hab
    apply e.injective
    apply Subtype.ext
    funext x
    calc
      (e a : ↥T).1 x = (p a).eval
          (Function.Embedding.subtype
            (fun z : F => z ∈ (S : Finset F)) x) := (hpeval a x).symm
      _ = (p b).eval
          (Function.Embedding.subtype
            (fun z : F => z ∈ (S : Finset F)) x) := by rw [hab]
      _ = (e b : ↥T).1 x := hpeval b x
  · intro j
    have hclose := hT (e j) (e j).property
    simp only [closeCodewordsRel, Set.mem_setOf_eq] at hclose
    have hball := hclose.2
    simp only [Code.relHammingBall, Set.mem_setOf_eq] at hball
    have hdec :
        (fun a b : F => Classical.propDecidable (a = b)) =
          (inferInstance : DecidableEq F) := Subsingleton.elim _ _
    rw [hdec] at hball
    have hball' :
        ((hammingDist y (e j : ↥T).1 : ℕ) : ℝ) / (n : ℝ) ≤
          rsRandomRadius ℓ k n η := by
      simpa only [Code.relHammingDist, NNRat.cast_div,
        NNRat.cast_natCast, Fintype.card_coe, S.property] using hball
    have hevalfun :
        (fun i : Fin n => (p j).eval (rsSubsetEmbedding S i)) =
          (e j : ↥T).1 ∘ rsSubsetIndexEquiv S := by
      funext i
      rw [rsSubsetEmbedding_apply]
      exact hpeval j (rsSubsetIndexEquiv S i)
    rw [hevalfun]
    rw [hammingDist_precomp_equiv (rsSubsetIndexEquiv S)]
    exact hball'

theorem rsEmbeddingImage_rsSubsetEmbedding
    {F : Type} [DecidableEq F] {n : ℕ}
    (S : {S : Finset F // S.card = n}) :
    rsEmbeddingImage n (rsSubsetEmbedding S) = S := by
  apply Subtype.ext
  change Finset.univ.map (rsSubsetEmbedding S) = (S : Finset F)
  ext x
  constructor
  · intro hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    rw [rsSubsetEmbedding_apply]
    exact (rsSubsetIndexEquiv S i).property
  · intro hx
    let i : Fin n := (rsSubsetIndexEquiv S).symm ⟨x, hx⟩
    apply Finset.mem_map.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [rsSubsetEmbedding_apply]
    change ((rsSubsetIndexEquiv S i : ↥(S : Finset F)) : F) = x
    simp only [i, Equiv.apply_symm_apply]

noncomputable def rsSubsetOrderEmbedding
    {F : Type} [DecidableEq F] {n : ℕ}
    (x : {S : Finset F // S.card = n} × Equiv.Perm (Fin n)) :
    Fin n ↪ F :=
  x.2.toEmbedding.trans (rsSubsetEmbedding x.1)

theorem rsEmbeddingImage_rsSubsetOrderEmbedding
    {F : Type} [DecidableEq F] {n : ℕ}
    (x : {S : Finset F // S.card = n} × Equiv.Perm (Fin n)) :
    rsEmbeddingImage n (rsSubsetOrderEmbedding x) = x.1 := by
  apply Subtype.ext
  change Finset.univ.map (x.2.toEmbedding.trans (rsSubsetEmbedding x.1)) =
    (x.1 : Finset F)
  rw [← Finset.map_map]
  rw [Finset.map_univ_equiv]
  exact congrArg Subtype.val (rsEmbeddingImage_rsSubsetEmbedding x.1)

theorem rsSubsetOrderEmbedding_injective
    {F : Type} [DecidableEq F] {n : ℕ} :
    Function.Injective (rsSubsetOrderEmbedding
      (F := F) (n := n)) := by
  intro x y hxy
  have hS : x.1 = y.1 := by
    calc
      x.1 = rsEmbeddingImage n (rsSubsetOrderEmbedding x) :=
        (rsEmbeddingImage_rsSubsetOrderEmbedding x).symm
      _ = rsEmbeddingImage n (rsSubsetOrderEmbedding y) := by rw [hxy]
      _ = y.1 := rsEmbeddingImage_rsSubsetOrderEmbedding y
  cases x with
  | mk S σ =>
      cases y with
      | mk T τ =>
          dsimp only at hS
          subst T
          apply Prod.ext
          · rfl
          · apply Equiv.ext
            intro i
            have hi := congrArg
              (fun e : Fin n ↪ F => e i) hxy
            change rsSubsetEmbedding S (σ i) =
              rsSubsetEmbedding S (τ i) at hi
            exact (rsSubsetEmbedding S).injective hi

def rsVertexZeroSet {t n : ℕ} (H : RSAgreementPattern t n)
    (v : Fin t) : Finset (Fin n) :=
  Finset.univ.filter fun i => v ∉ H i

def rsRootedGZPSet {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (a : RSRootedGZPIndex R) :
    Finset (Fin n) :=
  rsVertexZeroSet H a.1

theorem rsRootedGZP_commonZeros_eq_internalEdges
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k)
    (K : Finset (RSRootedGZPIndex R)) :
    (Finset.univ.filter fun i : Fin n =>
      ∀ a ∈ K, i ∈ rsRootedGZPSet R a) =
      rsPatternInternalEdges H
        ((Finset.univ : Finset (Fin t)) \ rsRootedGZPSupport R K) := by
  classical
  ext i
  rw [rsPatternInternalEdges]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h x hxH
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hxSupport
    rw [rsRootedGZPSupport] at hxSupport
    obtain ⟨a, haK, hax⟩ := Finset.mem_image.mp hxSupport
    have hzero := h a haK
    rw [rsRootedGZPSet, rsVertexZeroSet] at hzero
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzero
    apply hzero
    rw [hax]
    exact hxH
  · intro h a haK
    rw [rsRootedGZPSet, rsVertexZeroSet]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro haH
    have hsupp : a.1 ∈ rsRootedGZPSupport R K := by
      rw [rsRootedGZPSupport]
      exact Finset.mem_image.mpr ⟨a, haK, rfl⟩
    exact (Finset.mem_sdiff.mp (h haH)).2 hsupp

open scoped BigOperators in
theorem rsRootedGZPSet_isIndexedGZP
    {t n k : ℕ} {H : RSAgreementPattern t n}
    (R : RSRootedCutOrientation H k) (ht : 2 ≤ t) :
    rsIndexedGZP n (rsRootedGZPSet R) := by
  classical
  unfold rsIndexedGZP
  intro K hK
  let J : Finset (Fin t) := rsRootedGZPSupport R K
  have hJ : J.Nonempty := by
    dsimp only [J]
    exact rsRootedGZPSupport_nonempty R K hK
  have hInternal :=
    rsRootedGZP_internalEdges_le_sum_compl_multiplicity R ht J hJ
  have hKcard := rsRootedGZPIndex_card_le_sum_support_multiplicity R K
  rw [rsRootedGZP_commonZeros_eq_internalEdges R K]
  change (rsPatternInternalEdges H
      ((Finset.univ : Finset (Fin t)) \ J)).card + K.card ≤
    Fintype.card (RSRootedGZPIndex R)
  have hsplit := Finset.sum_sdiff (Finset.subset_univ J)
    (f := fun v : Fin t => rsRootedMultiplicity R v)
  calc
    (rsPatternInternalEdges H
        ((Finset.univ : Finset (Fin t)) \ J)).card + K.card ≤
        (∑ v ∈ (Finset.univ : Finset (Fin t)) \ J,
          rsRootedMultiplicity R v) +
        ∑ v ∈ J, rsRootedMultiplicity R v :=
      Nat.add_le_add hInternal (by simpa only [J] using hKcard)
    _ = ∑ v : Fin t, rsRootedMultiplicity R v := by
      exact hsplit
    _ = n - k := rsRootedMultiplicity_sum R ht
    _ = Fintype.card (RSRootedGZPIndex R) :=
      (rsRootedGZPIndex_card R ht).symm

noncomputable def rsWPCPatterns (t n k : ℕ) (η : ℝ) :
    Finset (RSAgreementPattern t n) := by
  classical
  exact Finset.univ.filter fun H =>
    rsPatternWeaklyPartitionConnected ((k : ℝ) + η * (n : ℝ)) H

noncomputable def rsAllWPCPatternBadEmbeddings
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) : Finset (Fin n ↪ F) := by
  classical
  exact (Finset.Icc 2 (ℓ + 1)).biUnion fun t =>
    (rsWPCPatterns t n k η).biUnion fun H =>
      rsFixedPatternBadEmbeddings (F := F) t n k H

theorem rsBadOrderedEmbeddings_subset_allWPCPattern
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) :
    rsBadOrderedEmbeddings (F := F) ℓ k n η ⊆
      rsAllWPCPatternBadEmbeddings (F := F) ℓ k n η := by
  classical
  intro α hα
  rw [rsBadOrderedEmbeddings, Finset.mem_filter] at hα
  rcases hα.2 with ⟨t, ht, htℓ, H, hWPC, hocc⟩
  rw [rsAllWPCPatternBadEmbeddings]
  apply Finset.mem_biUnion.mpr
  refine ⟨t, Finset.mem_Icc.mpr ⟨ht, htℓ⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨H, ?_, ?_⟩
  · rw [rsWPCPatterns, Finset.mem_filter]
    exact ⟨Finset.mem_univ H, hWPC⟩
  · rw [rsFixedPatternBadEmbeddings, Finset.mem_filter]
    exact ⟨Finset.mem_univ α, hocc⟩

theorem rsWPCPatterns_card_le (t n k : ℕ) (η : ℝ) :
    (rsWPCPatterns t n k η).card ≤ 2 ^ (t * n) := by
  classical
  calc
    (rsWPCPatterns t n k η).card ≤
        (Finset.univ : Finset (RSAgreementPattern t n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (RSAgreementPattern t n) := Finset.card_univ
    _ = 2 ^ (t * n) := card_RSAgreementPattern t n

open scoped BigOperators in
theorem rsWPC_exists_fullRankMinor_avoiding_of_erased_fullRank
    {F : Type} [Field F] {t n k : ℕ}
    (H : RSAgreementPattern t n) (root : Fin t)
    (B : Finset (Fin n)) (ht : 0 < t)
    (hWPC : rsPatternWeaklyPartitionConnected
      ((k : ℝ) + (B.card : ℝ)) H)
    (hfull : rsPatternWeaklyPartitionConnected (k : ℝ)
        (rsPatternEraseCoordinates H B) →
      rsRIMHasFullColumnRank (F := F)
        (rsPatternEraseCoordinates H B) root k) :
    ∃ ρ : RSRIMCol root k ↪ RSRIMRow H,
      (∀ c, (ρ c).1.1 ∉ B) ∧
        Matrix.det (rsRIMMinor (F := F) H root k ρ) ≠ 0 := by
  have herase := rsPatternErase_preserves_wpc H B ht (k : ℝ) hWPC
  exact rsPatternErase_fullRankMinor_avoiding H B root k (hfull herase)

open scoped BigOperators in
theorem rs_bad_ordered_union_patterns_card_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) :
    (rsBadOrderedEmbeddings (F := F) ℓ k n η).card ≤
      ∑ t ∈ Finset.Icc 2 (ℓ + 1),
        ∑ H : RSAgreementPattern t n,
          (rsFixedPatternBadEmbeddings (F := F) t n k H).card := by
  classical
  calc
    (rsBadOrderedEmbeddings (F := F) ℓ k n η).card ≤
        (rsAllPatternBadEmbeddings (F := F) ℓ k n).card :=
      Finset.card_le_card
        (rsBadOrderedEmbeddings_subset_allPattern ℓ k n η)
    _ ≤ ∑ t ∈ Finset.Icc 2 (ℓ + 1),
        ((Finset.univ : Finset (RSAgreementPattern t n)).biUnion fun H =>
          rsFixedPatternBadEmbeddings (F := F) t n k H).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.Icc 2 (ℓ + 1),
        ∑ H : RSAgreementPattern t n,
          (rsFixedPatternBadEmbeddings (F := F) t n k H).card := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (RSAgreementPattern t n)))
          (t := fun H => rsFixedPatternBadEmbeddings (F := F) t n k H))

open scoped BigOperators in
theorem rs_bad_ordered_union_wpc_patterns_card_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ k n : ℕ) (η : ℝ) :
    (rsBadOrderedEmbeddings (F := F) ℓ k n η).card ≤
      ∑ t ∈ Finset.Icc 2 (ℓ + 1),
        ∑ H ∈ rsWPCPatterns t n k η,
          (rsFixedPatternBadEmbeddings (F := F) t n k H).card := by
  classical
  calc
    (rsBadOrderedEmbeddings (F := F) ℓ k n η).card ≤
        (rsAllWPCPatternBadEmbeddings (F := F) ℓ k n η).card :=
      Finset.card_le_card
        (rsBadOrderedEmbeddings_subset_allWPCPattern ℓ k n η)
    _ ≤ ∑ t ∈ Finset.Icc 2 (ℓ + 1),
        ((rsWPCPatterns t n k η).biUnion fun H =>
          rsFixedPatternBadEmbeddings (F := F) t n k H).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.Icc 2 (ℓ + 1),
        ∑ H ∈ rsWPCPatterns t n k η,
          (rsFixedPatternBadEmbeddings (F := F) t n k H).card := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only using
        (Finset.card_biUnion_le
          (s := rsWPCPatterns t n k η)
          (t := fun H => rsFixedPatternBadEmbeddings (F := F) t n k H))

theorem rs_field_gap_lower
    {F : Type} [Fintype F] (ℓ k n : ℕ) (η : ℝ)
    (hF : (n : ℝ) + (k : ℝ) * 2 ^ ((10 * ℓ : ℝ) / η) ≤
      Fintype.card F) :
    (k : ℝ) * 2 ^ ((10 * ℓ : ℝ) / η) ≤
      (Fintype.card F : ℝ) - n := by
  linarith

theorem rs_total_ordered_embedding_card
    {F : Type} [Fintype F] [DecidableEq F] (n : ℕ) :
    Fintype.card (Fin n ↪ F) =
      Fintype.card {S : Finset F // S.card = n} * n.factorial := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_finset_len, Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.mul_comm _ _

open scoped BigOperators in
theorem sum_card_filter_swap
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (P : ι → κ → Prop) [∀ i j, Decidable (P i j)] :
    (∑ i : ι, ((Finset.univ.filter fun j : κ => P i j).card : ℝ)) =
      ∑ j : κ, ((Finset.univ.filter fun i : ι => P i j).card : ℝ) := by
  simp_rw [Finset.natCast_card_filter]
  rw [Finset.sum_comm]

open scoped BigOperators in
theorem rsBadPolynomialWitness_sum_pattern_card_lower
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} {α : Fin n ↪ F}
    (W : RSBadPolynomialWitness ℓ k n η α) (hn_pos : 0 < n) :
    (((ℓ + 1 : ℕ) : ℝ) * (n : ℝ) *
        (1 - rsRandomRadius ℓ k n η)) ≤
      ∑ i : Fin n, ((rsBadPolynomialWitnessPattern W i).card : ℝ) := by
  have hsum :
      (∑ _j : Fin (ℓ + 1),
          (n : ℝ) * (1 - rsRandomRadius ℓ k n η)) ≤
        ∑ j : Fin (ℓ + 1),
          ((Finset.univ.filter fun i : Fin n =>
            (W.p j).eval (α i) = W.y i).card : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    exact rsBadPolynomialWitness_agreement_card_lower W hn_pos j
  have hswap := sum_card_filter_swap
    (fun i : Fin n => fun j : Fin (ℓ + 1) =>
      (W.p j).eval (α i) = W.y i)
  calc
    (((ℓ + 1 : ℕ) : ℝ) * (n : ℝ) *
        (1 - rsRandomRadius ℓ k n η)) =
        ∑ _j : Fin (ℓ + 1),
          (n : ℝ) * (1 - rsRandomRadius ℓ k n η) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    _ ≤ ∑ j : Fin (ℓ + 1),
          ((Finset.univ.filter fun i : Fin n =>
            (W.p j).eval (α i) = W.y i).card : ℝ) := hsum
    _ = ∑ i : Fin n,
          ((rsBadPolynomialWitnessPattern W i).card : ℝ) := by
      simpa only [rsBadPolynomialWitnessPattern] using hswap.symm

open scoped BigOperators in
theorem rsBadPolynomialWitness_pattern_weight
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} {α : Fin n ↪ F}
    (W : RSBadPolynomialWitness ℓ k n η α) (hn_pos : 0 < n) :
    (ℓ : ℝ) * ((k : ℝ) + η * (n : ℝ)) ≤
      rsPatternSubsetWeight (rsBadPolynomialWitnessPattern W)
        (Finset.univ : Finset (Fin (ℓ + 1))) := by
  have hsum := rsBadPolynomialWitness_sum_pattern_card_lower W hn_pos
  have hweight := rsPatternSubsetWeight_univ_ge_sum_card_sub
    (rsBadPolynomialWitnessPattern W)
  have hid := rsRandomRadius_agreement_identity ℓ k n η hn_pos
  calc
    (ℓ : ℝ) * ((k : ℝ) + η * (n : ℝ)) =
        (((ℓ + 1 : ℕ) : ℝ) * (n : ℝ) *
          (1 - rsRandomRadius ℓ k n η)) - (n : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hid.symm
    _ ≤ (∑ i : Fin n,
          ((rsBadPolynomialWitnessPattern W i).card : ℝ)) - (n : ℝ) :=
      sub_le_sub_right hsum (n : ℝ)
    _ ≤ rsPatternSubsetWeight (rsBadPolynomialWitnessPattern W)
        (Finset.univ : Finset (Fin (ℓ + 1))) := hweight

open scoped BigOperators in
theorem sum_max_card_sub_one_eq_sum_card_sub_nonempty_count
    {α : Type} [DecidableEq α] (Q : Finset (Finset α)) (E : Finset α) :
    (∑ A ∈ Q, max (((A ∩ E).card : ℝ) - 1) 0) =
      (∑ A ∈ Q, ((A ∩ E).card : ℝ)) -
        ((Q.filter (fun A => (A ∩ E).Nonempty)).card : ℝ) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert A Q hAQ ih =>
      by_cases hne : (A ∩ E).Nonempty
      · have hcard : (1 : ℝ) ≤ ((A ∩ E).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr hne
        have hAfilter : A ∉ Q.filter (fun B => (B ∩ E).Nonempty) := by
          simp only [Finset.mem_filter, hAQ, false_and, not_false_eq_true]
        rw [Finset.filter_insert, if_pos hne,
          Finset.card_insert_of_notMem hAfilter]
        simp only [Finset.sum_insert, hAQ, not_false_eq_true, ih,
          max_eq_left (sub_nonneg.mpr hcard)]
        push_cast
        ring
      · have hempty : A ∩ E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        rw [Finset.filter_insert, if_neg hne]
        simp only [Finset.sum_insert, hAQ, not_false_eq_true, hempty,
          Finset.card_empty, Nat.cast_zero, zero_sub, ih]
        rw [max_eq_right (by norm_num : (-1 : ℝ) ≤ 0)]
        ring

open scoped BigOperators in
theorem rsPattern_edge_weight_eq_crossing_add_internal {t n : ℕ}
    (H : RSAgreementPattern t n) {J : Finset (Fin t)}
    (P : Finpartition J) (i : Fin n) :
    max (((J ∩ H i).card : ℝ) - 1) 0 =
      max ((((P.parts.filter (fun A => (A ∩ H i).Nonempty)).card : ℝ) - 1)) 0 +
        ∑ A ∈ P.parts, max (((A ∩ H i).card : ℝ) - 1) 0 := by
  classical
  have hsumReal :
      (∑ A ∈ P.parts, ((A ∩ H i).card : ℝ)) = ((J ∩ H i).card : ℝ) := by
    exact_mod_cast rsPattern_sum_inter_card_parts H P i
  have hinternal :=
    sum_max_card_sub_one_eq_sum_card_sub_nonempty_count P.parts (H i)
  rw [hsumReal] at hinternal
  by_cases hJE : (J ∩ H i).Nonempty
  · have htouched :
        (P.parts.filter (fun A => (A ∩ H i).Nonempty)).Nonempty := by
      obtain ⟨x, hx⟩ := hJE
      have hx' := Finset.mem_inter.mp hx
      obtain ⟨A, hA, hxA⟩ := P.exists_mem hx'.1
      refine ⟨A, Finset.mem_filter.mpr ⟨hA, ?_⟩⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hxA, hx'.2⟩⟩
    have hd : (1 : ℝ) ≤ ((J ∩ H i).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hJE
    have hm : (1 : ℝ) ≤
        ((P.parts.filter (fun A => (A ∩ H i).Nonempty)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr htouched
    rw [max_eq_left (sub_nonneg.mpr hd), max_eq_left (sub_nonneg.mpr hm)]
    linarith
  · have hJEempty : J ∩ H i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJE
    have htouchedEmpty :
        P.parts.filter (fun A => (A ∩ H i).Nonempty) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro A hA hnon
      obtain ⟨x, hx⟩ := hnon
      have hx' := Finset.mem_inter.mp hx
      have hxJ : x ∈ J := P.le hA hx'.1
      exact hJE ⟨x, Finset.mem_inter.mpr ⟨hxJ, hx'.2⟩⟩
    rw [hJEempty, htouchedEmpty] at hinternal ⊢
    norm_num at hinternal ⊢
    exact hinternal.symm

open scoped BigOperators in
theorem rsPatternSubsetWeight_eq_sum_parts_add_crossing {t n : ℕ}
    (H : RSAgreementPattern t n) {J : Finset (Fin t)}
    (P : Finpartition J) :
    rsPatternSubsetWeight H J =
      (∑ A ∈ P.parts, rsPatternSubsetWeight H A) +
        rsPatternCrossingWeightOn H P := by
  classical
  unfold rsPatternSubsetWeight rsPatternCrossingWeightOn
  calc
    (∑ i : Fin n, max (((J ∩ H i).card : ℝ) - 1) 0) =
        ∑ i : Fin n,
          (max ((((P.parts.filter
              (fun A => (A ∩ H i).Nonempty)).card : ℝ) - 1)) 0 +
            ∑ A ∈ P.parts, max (((A ∩ H i).card : ℝ) - 1) 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact rsPattern_edge_weight_eq_crossing_add_internal H P i
    _ = (∑ i : Fin n,
          max ((((P.parts.filter
            (fun A => (A ∩ H i).Nonempty)).card : ℝ) - 1)) 0) +
          ∑ i : Fin n, ∑ A ∈ P.parts,
            max (((A ∩ H i).card : ℝ) - 1) 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ A ∈ P.parts, ∑ i : Fin n,
            max (((A ∩ H i).card : ℝ) - 1) 0) +
          ∑ i : Fin n,
            max ((((P.parts.filter
              (fun A => (A ∩ H i).Nonempty)).card : ℝ) - 1)) 0 := by
      rw [Finset.sum_comm]
      ring

open scoped BigOperators in
theorem rs_exists_wpc_subset_of_weight {t n : ℕ}
    (H : RSAgreementPattern t n) (κ : ℝ) (hκ : 0 < κ) (ht : 2 ≤ t)
    (hweight : κ * ((t : ℝ) - 1) ≤
      rsPatternSubsetWeight H (Finset.univ : Finset (Fin t))) :
    ∃ J : Finset (Fin t),
      2 ≤ J.card ∧ rsPatternWeaklyPartitionConnectedOn κ H J := by
  classical
  let qualifies : ℕ → Prop := fun m =>
    ∃ J : Finset (Fin t),
      J.card = m ∧ 2 ≤ J.card ∧
        κ * ((J.card : ℝ) - 1) ≤ rsPatternSubsetWeight H J
  have hex : ∃ m, qualifies m := by
    refine ⟨t, Finset.univ, by simp, ?_, ?_⟩
    · simpa using ht
    · simpa using hweight
  let m : ℕ := Nat.find hex
  obtain ⟨J, hJcard, hJtwo, hJheavy⟩ := Nat.find_spec hex
  refine ⟨J, hJtwo, ?_⟩
  unfold rsPatternWeaklyPartitionConnectedOn
  intro P
  by_cases hPtriv : P.parts.card ≤ 1
  · have hJne : J ≠ ∅ := by
      intro hJempty
      rw [hJempty, Finset.card_empty] at hJtwo
      omega
    have hPne : P.parts ≠ ∅ := by
      intro hPempty
      exact hJne (P.parts_eq_empty_iff.mp hPempty)
    have hPcard : P.parts.card = 1 := by
      have hPpos : 0 < P.parts.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hPne)
      omega
    rw [hPcard]
    norm_num
    exact rsPatternCrossingWeightOn_nonneg H P
  · have hPtwo : 1 < P.parts.card := by omega
    have hpartBound : ∀ A ∈ P.parts,
        rsPatternSubsetWeight H A ≤ κ * ((A.card : ℝ) - 1) := by
      intro A hA
      have hAsub := rsFinpartition_part_ssubset_of_one_lt_card_parts P hPtwo hA
      by_cases hAcard : A.card ≤ 1
      · have hApos : 0 < A.card :=
          Finset.card_pos.mpr (P.nonempty_of_mem_parts hA)
        have hAone : A.card = 1 := by omega
        rw [rsPatternSubsetWeight_eq_zero_of_card_le_one H A hAcard, hAone]
        norm_num
      · have hAtwo : 2 ≤ A.card := by omega
        by_contra hbound
        have hrev : κ * ((A.card : ℝ) - 1) ≤ rsPatternSubsetWeight H A :=
          (lt_of_not_ge hbound).le
        have hpA : qualifies A.card := ⟨A, rfl, hAtwo, hrev⟩
        have hmin : m ≤ A.card := by
          dsimp [m]
          exact Nat.find_min' hex hpA
        have hcardLt : A.card < J.card := Finset.card_lt_card hAsub
        rw [hJcard] at hcardLt
        omega
    have hinternal :
        (∑ A ∈ P.parts, rsPatternSubsetWeight H A) ≤
          κ * ((J.card : ℝ) - (P.parts.card : ℝ)) := by
      calc
        (∑ A ∈ P.parts, rsPatternSubsetWeight H A) ≤
            ∑ A ∈ P.parts, κ * ((A.card : ℝ) - 1) := by
          exact Finset.sum_le_sum fun A hA => hpartBound A hA
        _ = κ * (∑ A ∈ P.parts, ((A.card : ℝ) - 1)) := by
          rw [Finset.mul_sum]
        _ = κ * ((J.card : ℝ) - (P.parts.card : ℝ)) := by
          rw [rsFinpartition_sum_card_sub_one P]
    have hdecomp := rsPatternSubsetWeight_eq_sum_parts_add_crossing H P
    linarith

open scoped BigOperators in
theorem rsBadPolynomialWitness_exists_wpc_pattern
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} {α : Fin n ↪ F}
    (W : RSBadPolynomialWitness ℓ k n η α)
    (hℓ_ge : 2 ≤ ℓ) (hη_pos : 0 < η) (hn_pos : 0 < n) :
    ∃ t, ∃ H : RSAgreementPattern t n,
      2 ≤ t ∧ t ≤ ℓ + 1 ∧ rsPatternOccurs t n k H α ∧
        rsPatternWeaklyPartitionConnected ((k : ℝ) + η * (n : ℝ)) H := by
  let κ : ℝ := (k : ℝ) + η * (n : ℝ)
  have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hκ : 0 < κ := by
    dsimp only [κ]
    have heta : 0 < η * (n : ℝ) := mul_pos hη_pos hn_real
    positivity
  have ht : 2 ≤ ℓ + 1 := by omega
  obtain ⟨J, hJtwo, hJwpc⟩ := rs_exists_wpc_subset_of_weight
    (rsBadPolynomialWitnessPattern W) κ hκ ht (by
      simpa only [κ, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, mul_comm]
        using rsBadPolynomialWitness_pattern_weight W hn_pos)
  refine ⟨J.card, rsPatternRestrict (rsBadPolynomialWitnessPattern W) J,
    hJtwo, ?_, ?_, ?_⟩
  · have hcard := Finset.card_le_card (Finset.subset_univ J)
    simpa only [Finset.card_univ, Fintype.card_fin] using hcard
  · exact rsPatternOccurs_restrict (rsBadPolynomialWitnessPattern W) J α
      (rsBadPolynomialWitness_pattern_occurs W)
  · simpa only [κ] using
      rsPatternWeaklyPartitionConnected_restrict
        (rsBadPolynomialWitnessPattern W) J κ hJwpc

open scoped BigOperators in
theorem rsBadPolynomialFamilyDomain_imp_badOrderedEmbedding
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} (S : {S : Finset F // S.card = n})
    (hℓ_ge : 2 ≤ ℓ) (hη_pos : 0 < η) (hn_pos : 0 < n)
    (hbad : rsBadPolynomialFamilyDomain ℓ k n η S) :
    rsBadOrderedEmbedding ℓ k n η (rsSubsetEmbedding S) := by
  obtain ⟨W⟩ :=
    rsBadPolynomialFamilyDomain_exists_badPolynomialWitness S hbad
  obtain ⟨t, H, ht, htℓ, hocc, hWPC⟩ :=
    rsBadPolynomialWitness_exists_wpc_pattern W hℓ_ge hη_pos hn_pos
  exact ⟨t, ht, htℓ, H, hWPC, hocc⟩

open scoped BigOperators in
theorem rsDomainBadList_exists_wpc_pattern
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ℓ k n : ℕ} {η : ℝ} (S : {S : Finset F // S.card = n})
    (hℓ_ge : 2 ≤ ℓ) (hη_pos : 0 < η) (hn_pos : 0 < n)
    (hbad : rsDomainBadList ℓ k n η S) :
    ∃ t, ∃ H : RSAgreementPattern t n,
      2 ≤ t ∧ t ≤ ℓ + 1 ∧
        rsPatternOccurs t n k H (rsSubsetEmbedding S) ∧
        rsPatternWeaklyPartitionConnected ((k : ℝ) + η * (n : ℝ)) H := by
  exact rsBadPolynomialWitness_exists_wpc_pattern
    (rsDomainBadList_to_badPolynomialWitness S hn_pos hbad)
    hℓ_ge hη_pos hn_pos

open scoped BigOperators in
theorem rs_bad_poly_domains_mul_factorial_le_bad_ordered
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ : ℕ) (hℓ_ge : 2 ≤ ℓ) (η : ℝ) (hη_pos : 0 < η)
    (k n : ℕ) (hn_pos : 0 < n) :
    (rsBadPolynomialFamilyDomains (F := F) ℓ k n η).card * n.factorial ≤
      (rsBadOrderedEmbeddings (F := F) ℓ k n η).card := by
  classical
  let emb :
      ({S : Finset F // S.card = n} × Equiv.Perm (Fin n)) ↪
        (Fin n ↪ F) :=
    ⟨rsSubsetOrderEmbedding, rsSubsetOrderEmbedding_injective⟩
  have hsub : (rsBadSubsetOrders (F := F) ℓ k n η).map emb ⊆
      rsBadOrderedEmbeddings (F := F) ℓ k n η := by
    intro α hα
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hα
    have hxprod := Finset.mem_product.mp hx
    have hSbad : rsBadPolynomialFamilyDomain ℓ k n η x.1 := by
      rw [rsBadPolynomialFamilyDomains] at hxprod
      exact (Finset.mem_filter.mp hxprod.1).2
    have hcanon := rsBadPolynomialFamilyDomain_imp_badOrderedEmbedding
      x.1 hℓ_ge hη_pos hn_pos hSbad
    have hordered := rsBadOrderedEmbedding_precomp_perm
      (rsSubsetEmbedding x.1) x.2 hcanon
    rw [rsBadOrderedEmbeddings, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change rsBadOrderedEmbedding ℓ k n η (rsSubsetOrderEmbedding x)
    exact hordered
  calc
    (rsBadPolynomialFamilyDomains (F := F) ℓ k n η).card * n.factorial =
        (rsBadPolynomialFamilyDomains (F := F) ℓ k n η).card *
          (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    _ = ((rsBadPolynomialFamilyDomains (F := F) ℓ k n η).product
          (Finset.univ : Finset (Equiv.Perm (Fin n)))).card :=
      (Finset.card_product _ _).symm
    _ = (rsBadSubsetOrders (F := F) ℓ k n η).card := rfl
    _ = ((rsBadSubsetOrders (F := F) ℓ k n η).map emb).card := by
      rw [Finset.card_map]
    _ ≤ (rsBadOrderedEmbeddings (F := F) ℓ k n η).card :=
      Finset.card_le_card hsub

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
  -- Expand the probability event with `ProbabilityTheory.Pr_eq_tsum_indicator` (or unfold
  -- the `Pr_` macro), reducing the lower bound to an upper bound on the uniform probability
  -- of bad subsets. For a fixed `S`, use
  -- `ListDecodable.Lambda_le_of_forall_finset_card_le` and represent each codeword by a
  -- degree-`< k` polynomial via `ReedSolomon.mem_code_iff_exists_polynomial`. Then apply the
  -- random-puncturing bad-family estimate. Keep the sample space exactly the size-`n` subtype.
  -- Assemble a per-subset bad-event characterization, a bound on the number of bad subsets,
  -- and the uniform-PMF cardinality calculation. Alternatively, bound the bad-event
  -- probability by `ENNReal.ofReal (2 ^ (-(ℓ * n : ℝ)))` and use complement arithmetic.
  sorry -- external admit: [AGL24, Theorem 1.1].

end RandomReedSolomon

end CodingTheory

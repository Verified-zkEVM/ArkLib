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

import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.SetTheory.Cardinal.Order
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

def bkrAddCircleInterval (a b : ℝ) : Set (AddCircle (1 : ℝ)) :=
  {z | a < ((AddCircle.equivIco (1 : ℝ) 0 z : _) : ℝ) ∧
    ((AddCircle.equivIco (1 : ℝ) 0 z : _) : ℝ) < b}

noncomputable def bkrAddCircleInterval_eq_image_Ioo
    (a b : ℝ) (ha0 : 0 ≤ a) (hb1 : b ≤ 1) :
    bkrAddCircleInterval a b =
      (fun x : ℝ => (x : AddCircle (1 : ℝ))) '' Set.Ioo a b := by
  ext z
  constructor
  · intro hz
    let x : ℝ := ((AddCircle.equivIco (1 : ℝ) 0 z : _) : ℝ)
    have hx : x ∈ Set.Ioo a b := by
      exact hz
    refine ⟨x, hx, ?_⟩
    change (AddCircle.equivIco (1 : ℝ) 0).symm
      (AddCircle.equivIco (1 : ℝ) 0 z) = z
    exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z
  · rintro ⟨x, hx, rfl⟩
    have hxIco : x ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      constructor <;> linarith [hx.1, hx.2]
    unfold bkrAddCircleInterval
    simp only [Set.mem_setOf_eq]
    rw [AddCircle.equivIco_coe_eq hxIco]
    exact hx

noncomputable def bkrAddCircleInterval_isOpen
    (a b : ℝ) (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1) :
    IsOpen (bkrAddCircleInterval a b) := by
  rw [bkrAddCircleInterval_eq_image_Ioo a b ha0.le hb1.le]
  exact QuotientAddGroup.isOpenMap_coe (Set.Ioo a b) isOpen_Ioo

noncomputable def bkrAddCircleInterval_nonempty
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) :
    (bkrAddCircleInterval a b).Nonempty := by
  let x : ℝ := (a + b) / 2
  have hxIco : x ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    dsimp only [x]
    constructor <;> linarith
  refine ⟨(x : AddCircle (1 : ℝ)), ?_⟩
  unfold bkrAddCircleInterval
  simp only [Set.mem_setOf_eq]
  rw [AddCircle.equivIco_coe_eq hxIco]
  dsimp only [x]
  constructor <;> linarith

noncomputable def bkrAddCircleInterval_nsmul_mem_iff
    (γ a b : ℝ) (m : ℕ) :
    m • (γ : AddCircle (1 : ℝ)) ∈ bkrAddCircleInterval a b ↔
      Int.fract (γ * (m : ℝ)) ∈ Set.Ioo a b := by
  have hcircle :
      m • (γ : AddCircle (1 : ℝ)) =
        ((γ * (m : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  rw [hcircle]
  unfold bkrAddCircleInterval
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  rw [AddCircle.coe_equivIco_mk_apply]
  norm_num

noncomputable def bkrAddCircleInterval_coe_mem_iff
    (x a b : ℝ) :
    (x : UnitAddCircle) ∈ bkrAddCircleInterval a b ↔
      Int.fract x ∈ Set.Ioo a b := by
  simpa only [one_nsmul, Nat.cast_one, mul_one] using
    (bkrAddCircleInterval_nsmul_mem_iff x a b 1)

noncomputable def bkrCeilError (x : ℝ) (m : ℕ) : ℝ :=
  (Nat.ceil (x * (m : ℝ)) : ℝ) - x * (m : ℝ)

noncomputable def bkrCeilError_eq_one_sub_fract
    (x : ℝ) (m : ℕ) (hx : 0 ≤ x)
    (hfract : Int.fract (x * (m : ℝ)) ≠ 0) :
    bkrCeilError x m = 1 - Int.fract (x * (m : ℝ)) := by
  unfold bkrCeilError
  rw [natCast_ceil_eq_intCast_ceil
    (mul_nonneg hx (Nat.cast_nonneg m))]
  exact Int.ceil_sub_self_eq hfract

noncomputable def bkrCeilError_eq_zero_of_fract_eq_zero
    (x : ℝ) (m : ℕ) (hx : 0 ≤ x)
    (hfract : Int.fract (x * (m : ℝ)) = 0) :
    bkrCeilError x m = 0 := by
  unfold bkrCeilError
  rw [natCast_ceil_eq_intCast_ceil
    (mul_nonneg hx (Nat.cast_nonneg m))]
  rcases Int.fract_eq_zero_iff.mp hfract with ⟨z, hz⟩
  rw [← hz, Int.ceil_intCast]
  norm_num

noncomputable def bkrCeilError_eq_zero_of_eq_intCast
    (x : ℝ) (m : ℕ) (hx : 0 ≤ x) (z : ℤ)
    (hxm : x * (m : ℝ) = (z : ℝ)) :
    bkrCeilError x m = 0 := by
  apply bkrCeilError_eq_zero_of_fract_eq_zero x m hx
  rw [hxm, Int.fract_intCast]

noncomputable def bkrCircleRepresentative (z : UnitAddCircle) : ℝ :=
  ((AddCircle.equivIco (1 : ℝ) (-(1 : ℝ) / 2) z : _) : ℝ)

noncomputable def bkrCircleEndomorphismRepresentative
    (φ : UnitAddCircle →ₜ+ UnitAddCircle) (x : ℝ) : ℝ :=
  bkrCircleRepresentative (φ (x : UnitAddCircle))

noncomputable def bkrCircleRepresentative_coe (z : UnitAddCircle) :
    (bkrCircleRepresentative z : UnitAddCircle) = z := by
  change (AddCircle.equivIco (1 : ℝ) (-(1 : ℝ) / 2)).symm
    (AddCircle.equivIco (1 : ℝ) (-(1 : ℝ) / 2) z) = z
  exact (AddCircle.equivIco (1 : ℝ) (-(1 : ℝ) / 2)).symm_apply_apply z

noncomputable def bkrCircleEndomorphismRepresentative_coe
    (φ : UnitAddCircle →ₜ+ UnitAddCircle) (x : ℝ) :
    (bkrCircleEndomorphismRepresentative φ x : UnitAddCircle) =
      φ (x : UnitAddCircle) := by
  exact bkrCircleRepresentative_coe _

noncomputable def bkrCircleRepresentative_continuousAt_zero :
    ContinuousAt bkrCircleRepresentative (0 : UnitAddCircle) := by
  unfold bkrCircleRepresentative
  apply continuous_subtype_val.continuousAt.comp
  apply AddCircle.continuousAt_equivIco
  change ((0 : ℝ) : UnitAddCircle) ≠
    ((-(1 : ℝ) / 2 : ℝ) : UnitAddCircle)
  intro h
  have h0 : (0 : ℝ) ∈
      Set.Ico (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1) := by
    constructor <;> norm_num
  have ha : (-(1 : ℝ) / 2) ∈
      Set.Ico (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1) := by
    constructor <;> norm_num
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico h0 ha).mp h
  norm_num at heq

noncomputable def bkrCircleEndomorphismRepresentative_continuousAt_zero
    (φ : UnitAddCircle →ₜ+ UnitAddCircle) :
    ContinuousAt (bkrCircleEndomorphismRepresentative φ) 0 := by
  change ContinuousAt
    (fun x : ℝ => bkrCircleRepresentative (φ (x : UnitAddCircle))) 0
  have hin : ContinuousAt (fun x : ℝ => φ (x : UnitAddCircle)) 0 :=
    (φ.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).continuousAt
  exact bkrCircleRepresentative_continuousAt_zero.comp_of_eq
    hin (by simp only [AddCircle.coe_zero, map_zero])

noncomputable def bkrCircleRepresentative_mem_Ico (z : UnitAddCircle) :
    bkrCircleRepresentative z ∈
      Set.Ico (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1) := by
  exact (AddCircle.equivIco (1 : ℝ) (-(1 : ℝ) / 2) z).property

noncomputable def bkrCircleRepresentative_zero :
    bkrCircleRepresentative (0 : UnitAddCircle) = 0 := by
  have h0 : (0 : ℝ) ∈
      Set.Ico (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1) := by
    constructor <;> norm_num
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (bkrCircleRepresentative_mem_Ico 0) h0).mp
  rw [bkrCircleRepresentative_coe]
  exact (AddCircle.coe_zero (1 : ℝ)).symm

noncomputable def bkrCircleEndomorphismRepresentative_zero
    (φ : UnitAddCircle →ₜ+ UnitAddCircle) :
    bkrCircleEndomorphismRepresentative φ 0 = 0 := by
  unfold bkrCircleEndomorphismRepresentative
  rw [AddCircle.coe_zero, map_zero, bkrCircleRepresentative_zero]

noncomputable def bkrCoefficientProfile_card
    {F : Type} [Fintype F]
    (m u v : ℕ) (hcard : Fintype.card F = 2 ^ m) :
    Nat.card ({j : ℕ // j ∈ Finset.Ico (u + 1) v} → F) =
      (2 ^ m) ^ (v - u - 1) := by
  classical
  letI : Fintype {j : ℕ // j ∈ Finset.Ico (u + 1) v} :=
    Fintype.ofFinite _
  have hsub : v - (u + 1) = v - u - 1 := by omega
  rw [Nat.card_fun]
  rw [Nat.card_eq_fintype_card, hcard]
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_Ico, hsub]

noncomputable def bkrCoordinateEquiv
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (m v : ℕ) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m) :
    ((Fin v → ZMod 2) × (Fin (m - v) → ZMod 2)) ≃ₗ[ZMod 2] F := by
  apply LinearEquiv.ofFinrankEq
  rw [Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_fin_fun, hfin]
  omega

def bkrGoodRounding (α β : ℝ) (m : ℕ) : Prop :=
  let a := bkrCeilError α m
  let b := bkrCeilError β m
  (a = 0 ∧ b = 0) ∨
    2 * β * b + b ^ 2 / (m : ℝ) ≤ a

def bkrGoodRoundingWindow (α β ε : ℝ) (m : ℕ) : Prop :=
  let a := bkrCeilError α m
  let b := bkrCeilError β m
  (a = 0 ∧ b = 0) ∨
    (ε ≤ Int.fract (α * (m : ℝ)) ∧
      2 * β * b + b ^ 2 / (m : ℝ) ≤ a)

noncomputable def bkrGoodRoundingWindow_of_beta_fract_zero
    (α β ε : ℝ) (m : ℕ) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hfa0 : Int.fract (α * (m : ℝ)) ≠ 0)
    (hfb0 : Int.fract (β * (m : ℝ)) = 0)
    (hε : ε ≤ Int.fract (α * (m : ℝ))) :
    bkrGoodRoundingWindow α β ε m := by
  unfold bkrGoodRoundingWindow
  dsimp only
  right
  refine ⟨hε, ?_⟩
  rw [bkrCeilError_eq_one_sub_fract α m hα0 hfa0]
  rw [bkrCeilError_eq_zero_of_fract_eq_zero β m hβ0 hfb0]
  have hfract := Int.fract_lt_one (α * (m : ℝ))
  norm_num
  linarith

noncomputable def bkrGoodRoundingWindow_of_fract_bounds
    (α β ε η A : ℝ) (m : ℕ)
    (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hm : 0 < m)
    (hη0 : 0 ≤ η)
    (hfa0 : Int.fract (α * (m : ℝ)) ≠ 0)
    (hfb0 : Int.fract (β * (m : ℝ)) ≠ 0)
    (hε : ε ≤ Int.fract (α * (m : ℝ)))
    (hfaA : Int.fract (α * (m : ℝ)) ≤ A)
    (hfbη : 1 - η ≤ Int.fract (β * (m : ℝ)))
    (hineq : 2 * β * η + η ^ 2 / (m : ℝ) ≤ 1 - A) :
    bkrGoodRoundingWindow α β ε m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hfa_lt := Int.fract_lt_one (α * (m : ℝ))
  have hfb_lt := Int.fract_lt_one (β * (m : ℝ))
  have hb0 : 0 ≤ 1 - Int.fract (β * (m : ℝ)) := by linarith
  have hbη : 1 - Int.fract (β * (m : ℝ)) ≤ η := by linarith
  have hlinear :
      2 * β * (1 - Int.fract (β * (m : ℝ))) ≤ 2 * β * η := by
    exact mul_le_mul_of_nonneg_left hbη (mul_nonneg (by norm_num) hβ0)
  have hsquare :
      (1 - Int.fract (β * (m : ℝ))) ^ 2 ≤ η ^ 2 := by
    nlinarith
  have hdiv :
      (1 - Int.fract (β * (m : ℝ))) ^ 2 / (m : ℝ) ≤
        η ^ 2 / (m : ℝ) :=
    div_le_div_of_nonneg_right hsquare hmR.le
  have hround :
      2 * β * (1 - Int.fract (β * (m : ℝ))) +
          (1 - Int.fract (β * (m : ℝ))) ^ 2 / (m : ℝ) ≤
        1 - Int.fract (α * (m : ℝ)) := by
    linarith
  unfold bkrGoodRoundingWindow
  dsimp only
  right
  refine ⟨hε, ?_⟩
  rw [bkrCeilError_eq_one_sub_fract α m hα0 hfa0]
  rw [bkrCeilError_eq_one_sub_fract β m hβ0 hfb0]
  exact hround

def bkrGraphFamily
    (K A B : Type) [Semiring K] [AddCommMonoid A] [Module K A]
    [AddCommMonoid B] [Module K B] : Set (Submodule K (A × B)) :=
  Set.range fun f : A →ₗ[K] B => f.graph

noncomputable def bkrGraph_finrank
    {K A B : Type} [DivisionRing K] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [Module.Finite K A]
    (f : A →ₗ[K] B) :
    Module.finrank K f.graph = Module.finrank K A := by
  rw [LinearMap.graph_eq_range_prod]
  apply LinearMap.finrank_range_of_inj
  intro x y hxy
  exact congrArg Prod.fst hxy

def bkrGraph_injective
    {K A B : Type} [Semiring K] [AddCommMonoid A] [Module K A]
    [AddCommMonoid B] [Module K B] :
    Function.Injective (fun f : A →ₗ[K] B => f.graph) := by
  intro f g hfg
  change f.graph = g.graph at hfg
  apply LinearMap.ext
  intro x
  have hx : (x, f x) ∈ f.graph := by
    rw [LinearMap.mem_graph_iff]
  rw [hfg] at hx
  exact (LinearMap.mem_graph_iff (f := g) (x, f x)).mp hx

noncomputable def bkrGraphFamily_ncard
    {K A B : Type} [Field K] [Fintype K]
    [AddCommGroup A] [Module K A] [Module.Finite K A]
    [AddCommGroup B] [Module K B] [Module.Finite K B] :
    (bkrGraphFamily K A B).ncard =
      Fintype.card K ^
        (Module.finrank K A * Module.finrank K B) := by
  letI : Module.Finite K (A →ₗ[K] B) :=
    Module.Finite.linearMap K K A B
  rw [bkrGraphFamily]
  rw [Set.ncard_range_of_injective bkrGraph_injective]
  rw [@Module.natCard_eq_pow_finrank K (A →ₗ[K] B)]
  rw [Module.finrank_linearMap K K A B]
  rw [Nat.card_eq_fintype_card]

noncomputable def bkrCoordinateGraphFamily_ncard
    (v w : ℕ) :
    (bkrGraphFamily (ZMod 2) (Fin v → ZMod 2)
      (Fin w → ZMod 2)).ncard = 2 ^ (v * w) := by
  simpa only [ZMod.card, Module.finrank_fin_fun] using
    (bkrGraphFamily_ncard
      (K := ZMod 2) (A := Fin v → ZMod 2) (B := Fin w → ZMod 2))

noncomputable def bkrGraphParameter_card
    (m v : ℕ) :
    Nat.card ((Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) = 2 ^ (v * (m - v)) := by
  rw [← Set.ncard_range_of_injective
    (bkrGraph_injective : Function.Injective
      (fun f : (Fin v → ZMod 2) →ₗ[ZMod 2]
        (Fin (m - v) → ZMod 2) => f.graph))]
  exact bkrCoordinateGraphFamily_ncard v (m - v)

noncomputable def bkrLocalAdditiveExtensionIndex
    (δ x : ℝ) : ℕ :=
  Nat.ceil (|x| / δ) + 1

noncomputable def bkrLocalAdditiveExtension
    (g : ℝ → ℝ) (δ x : ℝ) : ℝ :=
  let n := bkrLocalAdditiveExtensionIndex δ x
  (n : ℝ) * g (x / (n : ℝ))

def bkrLooseParameters (α β : ℝ) (m u v : ℕ) : Prop :=
  0 < m ∧ u < v ∧ v ≤ m ∧
    v ^ 2 ≤ (u + 1) * m ∧
    2 ^ u < Nat.floor ((((2 ^ m : ℕ) : ℝ) ^ α)) ∧
    1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m ≤
      1 - (((2 ^ m : ℕ) : ℝ) ^ (β - 1)) ∧
    (((2 ^ m : ℕ) : ℝ) ^
        ((α - β ^ 2) * Real.logb 2 (2 ^ m : ℕ))) ≤
      (2 : ℝ) ^ ((((u + 1) * m - v ^ 2 : ℕ) : ℝ))

def bkrOrbitClosure (α β : ℝ) :
    AddSubgroup (UnitAddCircle × UnitAddCircle) :=
  (AddSubgroup.zmultiples
    ((α : UnitAddCircle), (β : UnitAddCircle))).topologicalClosure

def bkrHorizontalKernel (α β : ℝ) : AddSubgroup UnitAddCircle :=
  (bkrOrbitClosure α β).comap
    (AddMonoidHom.inl UnitAddCircle UnitAddCircle)

def bkrHorizontalKernel_mem_iff (α β : ℝ) (a : UnitAddCircle) :
    a ∈ bkrHorizontalKernel α β ↔
      (a, 0) ∈ bkrOrbitClosure α β := by
  rfl

def bkrOrbitClosureClosed (α β : ℝ) :
    ClosedAddSubgroup (UnitAddCircle × UnitAddCircle) :=
  ClosedAddSubgroup.mk (bkrOrbitClosure α β)
    (AddSubgroup.isClosed_topologicalClosure _)

noncomputable def bkrOrbitFst (α β : ℝ) :
    bkrOrbitClosureClosed α β →ₜ+ UnitAddCircle :=
  ContinuousAddMonoidHom.mk
    ((AddMonoidHom.fst UnitAddCircle UnitAddCircle).comp
      (AddSubgroupClass.subtype (bkrOrbitClosureClosed α β)))
    (continuous_fst.comp continuous_subtype_val)

def bkrOrbitFst_apply (α β : ℝ)
    (z : bkrOrbitClosureClosed α β) :
    bkrOrbitFst α β z = z.1.1 := rfl

noncomputable def bkrOrbitGenerator (α β : ℝ) :
    bkrOrbitClosureClosed α β := by
  let x : UnitAddCircle × UnitAddCircle :=
    ((α : UnitAddCircle), (β : UnitAddCircle))
  refine ⟨x, ?_⟩
  exact AddSubgroup.le_topologicalClosure _
    (AddSubgroup.mem_zmultiples x)

def bkrOrbitGenerator_fst (α β : ℝ) :
    (bkrOrbitGenerator α β).1.1 = (α : UnitAddCircle) := rfl

def bkrOrbitGenerator_snd (α β : ℝ) :
    (bkrOrbitGenerator α β).1.2 = (β : UnitAddCircle) := rfl

noncomputable def bkrOrbitSnd (α β : ℝ) :
    bkrOrbitClosureClosed α β →ₜ+ UnitAddCircle :=
  ContinuousAddMonoidHom.mk
    ((AddMonoidHom.snd UnitAddCircle UnitAddCircle).comp
      (AddSubgroupClass.subtype (bkrOrbitClosureClosed α β)))
    (continuous_snd.comp continuous_subtype_val)

def bkrOrbitSnd_apply (α β : ℝ)
    (z : bkrOrbitClosureClosed α β) :
    bkrOrbitSnd α β z = z.1.2 := rfl

noncomputable def bkrSubspaceCoordinateEmbedding
    {ι F : Type} (e : ι ≃ F) [Field F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) : L ↪ ι :=
  ⟨fun x => e.symm (x : F), fun _ _ h =>
    Subtype.ext (e.symm.injective h)⟩

noncomputable def bkrSubspaceCoordinateFinset
    {ι F : Type} [Fintype F] (e : ι ≃ F)
    [Field F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) : Finset ι := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  exact Finset.univ.map (bkrSubspaceCoordinateEmbedding e L)

noncomputable def bkrSubspaceCoordinateFinset_card
    {ι F : Type} [Fintype F] (e : ι ≃ F)
    [Field F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    (bkrSubspaceCoordinateFinset e L).card = 2 ^ v := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  calc
    (bkrSubspaceCoordinateFinset e L).card = Fintype.card L := by
      unfold bkrSubspaceCoordinateFinset
      rw [Finset.card_map, Finset.card_univ]
    _ = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) L :=
      Module.card_eq_pow_finrank
    _ = 2 ^ v := by rw [ZMod.card, hfin]

noncomputable def bkrSubspaceCoordinateFinset_mem
    {ι F : Type} [Fintype F] (e : ι ≃ F)
    [Field F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (i : ι)
    (hi : i ∈ bkrSubspaceCoordinateFinset e L) : e i ∈ L := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  unfold bkrSubspaceCoordinateFinset at hi
  rcases Finset.mem_map.mp hi with ⟨x, _hx, hxi⟩
  change e i ∈ L
  rw [← hxi]
  change e (e.symm (x : F)) ∈ L
  rw [e.apply_symm_apply]
  exact x.property

def bkrSubspaceFamily
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (v : ℕ) : Set (Submodule (ZMod 2) F) :=
  {L | Module.finrank (ZMod 2) L = v}

noncomputable def bkrTransportedGraph
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (m v : ℕ) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m)
    (f : (Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) : Submodule (ZMod 2) F :=
  f.graph.map (bkrCoordinateEquiv m v hvm hfin).toLinearMap

noncomputable def bkrTransportedGraphFamily
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (m v : ℕ) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m) :
    Set (Submodule (ZMod 2) F) :=
  Set.range (bkrTransportedGraph m v hvm hfin)

noncomputable def bkrTransportedGraph_finrank
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (m v : ℕ) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m)
    (f : (Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) :
    Module.finrank (ZMod 2) (bkrTransportedGraph m v hvm hfin f) = v := by
  unfold bkrTransportedGraph
  rw [LinearEquiv.finrank_map_eq]
  rw [bkrGraph_finrank]
  exact Module.finrank_fin_fun (ZMod 2)

noncomputable def bkrTransportedGraph_injective
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (m v : ℕ) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m) :
    Function.Injective (bkrTransportedGraph m v hvm hfin) := by
  intro f g hfg
  apply bkrGraph_injective
  exact (Submodule.map_injective_of_injective
    (bkrCoordinateEquiv m v hvm hfin).injective) hfg

noncomputable def bkrTransportedGraphFamily_ncard
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (m v : ℕ) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m) :
    (bkrTransportedGraphFamily m v hvm hfin).ncard =
      2 ^ (v * (m - v)) := by
  rw [bkrTransportedGraphFamily]
  rw [Set.ncard_range_of_injective
    (bkrTransportedGraph_injective m v hvm hfin)]
  rw [← Set.ncard_range_of_injective
    (bkrGraph_injective : Function.Injective
      (fun f : (Fin v → ZMod 2) →ₗ[ZMod 2]
        (Fin (m - v) → ZMod 2) => f.graph))]
  exact bkrCoordinateGraphFamily_ncard v (m - v)

noncomputable def bkr_addCircle_denseRange_zsmul_of_irrational
    (γ : ℝ) (hγ : Irrational γ) :
    DenseRange (fun n : ℤ => n • (γ : AddCircle (1 : ℝ))) := by
  exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hγ)

noncomputable def bkr_ceil_parameters_order
    (α β : ℝ) (m : ℕ) (hαpos : 0 < α) (hαβ : α < β)
    (hβ1 : β < 1) (hm : 0 < m) :
    Nat.ceil (α * (m : ℝ)) - 1 < Nat.ceil (β * (m : ℝ)) ∧
      Nat.ceil (β * (m : ℝ)) ≤ m := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hαm : 0 < α * (m : ℝ) := mul_pos hαpos hmreal
  have hmul : α * (m : ℝ) ≤ β * (m : ℝ) :=
    mul_le_mul_of_nonneg_right (le_of_lt hαβ) (le_of_lt hmreal)
  have hceil : Nat.ceil (α * (m : ℝ)) ≤ Nat.ceil (β * (m : ℝ)) :=
    Nat.ceil_mono hmul
  have hUpos : 0 < Nat.ceil (α * (m : ℝ)) := Nat.ceil_pos.mpr hαm
  constructor
  · omega
  · rw [Nat.ceil_le]
    nlinarith [mul_pos (sub_pos.mpr hβ1) hmreal]

noncomputable def bkr_ceil_sub_one_eq_floor
    (x : ℝ) (m : ℕ) (hx : 0 ≤ x)
    (hfract : Int.fract (x * (m : ℝ)) ≠ 0) :
    Nat.ceil (x * (m : ℝ)) - 1 =
      Nat.floor (x * (m : ℝ)) := by
  have hy : 0 ≤ x * (m : ℝ) :=
    mul_nonneg hx (Nat.cast_nonneg m)
  have hnotmem :
      x * (m : ℝ) ∉ Set.range ((↑) : ℤ → ℝ) := by
    exact fun hmem => hfract (Int.fract_eq_zero_iff.mpr hmem)
  have hint :
      Int.ceil (x * (m : ℝ)) =
        Int.floor (x * (m : ℝ)) + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem
      (x * (m : ℝ))).mpr hnotmem
  have hz :
      (Nat.ceil (x * (m : ℝ)) : ℤ) =
        (Nat.floor (x * (m : ℝ)) : ℤ) + 1 := by
    rw [Int.natCast_ceil_eq_ceil hy,
      Int.natCast_floor_eq_floor hy]
    exact hint
  omega

open Filter Topology in
noncomputable def
    bkr_circle_endomorphism_representative_locally_additive
    (φ : UnitAddCircle →ₜ+ UnitAddCircle) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (x y : ℝ), |x| < δ → |y| < δ → |x + y| < δ →
        bkrCircleEndomorphismRepresentative φ (x + y) =
          bkrCircleEndomorphismRepresentative φ x +
            bkrCircleEndomorphismRepresentative φ y := by
  let g : ℝ → ℝ := bkrCircleEndomorphismRepresentative φ
  have hg0 : g 0 = 0 := bkrCircleEndomorphismRepresentative_zero φ
  have hgcont : ContinuousAt g 0 :=
    bkrCircleEndomorphismRepresentative_continuousAt_zero φ
  have hnhds : Set.Ioo (-(1 : ℝ) / 6) (1 / 6) ∈ 𝓝 (g 0) := by
    rw [hg0]
    exact Ioo_mem_nhds (by norm_num) (by norm_num)
  have hpre : g ⁻¹' Set.Ioo (-(1 : ℝ) / 6) (1 / 6) ∈ 𝓝 (0 : ℝ) :=
    hgcont hnhds
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun x y hx hy hxy => ?_⟩
  have hxball : x ∈ Metric.ball (0 : ℝ) δ :=
    mem_ball_zero_iff.mpr (by simpa only [Real.norm_eq_abs] using hx)
  have hyball : y ∈ Metric.ball (0 : ℝ) δ :=
    mem_ball_zero_iff.mpr (by simpa only [Real.norm_eq_abs] using hy)
  have hxyball : x + y ∈ Metric.ball (0 : ℝ) δ :=
    mem_ball_zero_iff.mpr (by simpa only [Real.norm_eq_abs] using hxy)
  have hgx : g x ∈ Set.Ioo (-(1 : ℝ) / 6) (1 / 6) := hball hxball
  have hgy : g y ∈ Set.Ioo (-(1 : ℝ) / 6) (1 / 6) := hball hyball
  have hgxy : g (x + y) ∈ Set.Ioo (-(1 : ℝ) / 6) (1 / 6) :=
    hball hxyball
  rcases hgx with ⟨hgxl, hgxu⟩
  rcases hgy with ⟨hgyl, hgyu⟩
  rcases hgxy with ⟨hgxyl, hgxyu⟩
  have hleft : g (x + y) ∈
      Set.Ico (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1) := by
    constructor <;> linarith
  have hright : g x + g y ∈
      Set.Ico (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1) := by
    constructor <;> linarith
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico hleft hright).mp
  calc
    (bkrCircleEndomorphismRepresentative φ (x + y) : UnitAddCircle) =
        φ ((x + y : ℝ) : UnitAddCircle) :=
      bkrCircleEndomorphismRepresentative_coe φ (x + y)
    _ = φ ((x : UnitAddCircle) + (y : UnitAddCircle)) :=
      congrArg φ (AddCircle.coe_add (1 : ℝ) x y)
    _ = φ (x : UnitAddCircle) + φ (y : UnitAddCircle) := φ.map_add _ _
    _ = (bkrCircleEndomorphismRepresentative φ x : UnitAddCircle) +
        (bkrCircleEndomorphismRepresentative φ y : UnitAddCircle) := by
      rw [bkrCircleEndomorphismRepresentative_coe,
        bkrCircleEndomorphismRepresentative_coe]
    _ = ((bkrCircleEndomorphismRepresentative φ x +
        bkrCircleEndomorphismRepresentative φ y : ℝ) : UnitAddCircle) :=
      (AddCircle.coe_add (1 : ℝ)
        (bkrCircleEndomorphismRepresentative φ x)
        (bkrCircleEndomorphismRepresentative φ y)).symm

open Filter Topology in
noncomputable def bkr_circle_endomorphism_representative_nat_mul
    (φ : UnitAddCircle →ₜ+ UnitAddCircle) (δ : ℝ) (hδ : 0 < δ)
    (hadd : ∀ (x y : ℝ), |x| < δ → |y| < δ → |x + y| < δ →
      bkrCircleEndomorphismRepresentative φ (x + y) =
        bkrCircleEndomorphismRepresentative φ x +
          bkrCircleEndomorphismRepresentative φ y)
    (n : ℕ) (x : ℝ) (hx : |(n : ℝ) * x| < δ) :
    bkrCircleEndomorphismRepresentative φ ((n : ℝ) * x) =
      (n : ℝ) * bkrCircleEndomorphismRepresentative φ x := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul]
      rw [bkrCircleEndomorphismRepresentative_zero]
  | succ n ih =>
      have hcast0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hcast1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos n
      have habs_succ :
          |((n + 1 : ℕ) : ℝ) * x| =
            ((n + 1 : ℕ) : ℝ) * |x| := by
        rw [abs_mul, abs_of_nonneg]
        positivity
      have hscaled : ((n + 1 : ℕ) : ℝ) * |x| < δ := by
        rw [← habs_succ]
        exact hx
      have hxsmall : |x| < δ := by
        have hle : |x| ≤ ((n + 1 : ℕ) : ℝ) * |x| := by
          nlinarith [abs_nonneg x]
        exact hle.trans_lt hscaled
      have hnscaled : (n : ℝ) * |x| < δ := by
        have hle : (n : ℝ) * |x| ≤
            ((n + 1 : ℕ) : ℝ) * |x| := by
          norm_num only [Nat.cast_add, Nat.cast_one]
          nlinarith [abs_nonneg x]
        exact hle.trans_lt hscaled
      have hnsmall : |(n : ℝ) * x| < δ := by
        rw [abs_mul, abs_of_nonneg hcast0]
        exact hnscaled
      have hsumsmall : |(n : ℝ) * x + x| < δ := by
        convert hx using 1 <;> push_cast <;> ring
      have hlocal := hadd ((n : ℝ) * x) x hnsmall hxsmall hsumsmall
      rw [show ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x by
        push_cast
        ring]
      rw [hlocal, ih hnsmall]
      push_cast
      ring

noncomputable def bkr_circle_relation_integer_cases
    (α β : ℝ) (hα_pos : 0 < α) (hα_lt : α < β)
    (hβ_lt : β < 1) (k : ℤ)
    (hrel : (α : UnitAddCircle) = k • (β : UnitAddCircle)) :
    k < 0 ∨ 2 ≤ k := by
  have hk0 : k ≠ 0 := by
    intro hk
    subst k
    simp only [zero_zsmul] at hrel
    obtain ⟨n, hn⟩ :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hrel
    have hn' : (n : ℝ) = α := by
      simpa only [zsmul_eq_mul, mul_one] using hn
    have hnposR : (0 : ℝ) < (n : ℝ) := by
      rw [hn']
      exact hα_pos
    have hnltR : (n : ℝ) < 1 := by
      rw [hn']
      exact hα_lt.trans hβ_lt
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hnposR
    have hnlt : n < 1 := by exact_mod_cast hnltR
    omega
  have hk1 : k ≠ 1 := by
    intro hk
    subst k
    simp only [one_zsmul] at hrel
    have hzero : ((α - β : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hrel, sub_self]
    obtain ⟨n, hn⟩ :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
    have hn' : (n : ℝ) = α - β := by
      simpa only [zsmul_eq_mul, mul_one] using hn
    have hnnegR : (n : ℝ) < 0 := by
      rw [hn']
      linarith
    have hnlowR : (-1 : ℝ) < (n : ℝ) := by
      rw [hn']
      linarith
    have hnneg : n < 0 := by exact_mod_cast hnnegR
    have hnlow : (-1 : ℤ) < n := by exact_mod_cast hnlowR
    omega
  omega

open Filter in
noncomputable def bkr_degree_slack_eventually
    (α ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      1 < (2 : ℝ) ^ Nat.floor (α * (m : ℝ)) *
        ((2 : ℝ) ^ ε - 1) := by
  have hgap : 0 < (2 : ℝ) ^ ε - 1 := by
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) hε)
  obtain ⟨R, hR⟩ :=
    pow_unbounded_of_one_lt (1 / ((2 : ℝ) ^ ε - 1))
      (by norm_num : (1 : ℝ) < 2)
  have hRslack :
      1 < (2 : ℝ) ^ R * ((2 : ℝ) ^ ε - 1) := by
    calc
      1 = (1 / ((2 : ℝ) ^ ε - 1)) * ((2 : ℝ) ^ ε - 1) := by
        field_simp
      _ < (2 : ℝ) ^ R * ((2 : ℝ) ^ ε - 1) :=
        mul_lt_mul_of_pos_right hR hgap
  have hevent :
      ∀ᶠ m : ℕ in Filter.atTop,
        R ≤ Nat.floor (α * (m : ℝ)) :=
    (Filter.tendsto_atTop.1 (tendsto_nat_floor_mul_atTop α hα)) R
  rcases Filter.eventually_atTop.1 hevent with ⟨m₀, hm₀⟩
  refine ⟨m₀, fun m hm => ?_⟩
  have hpow :
      (2 : ℝ) ^ R ≤ (2 : ℝ) ^ Nat.floor (α * (m : ℝ)) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (hm₀ m hm)
  exact hRslack.trans_le (mul_le_mul_of_nonneg_right hpow hgap.le)

noncomputable def bkr_fract_eq_of_addCircle_eq
    (x r : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) 1)
    (h : (x : UnitAddCircle) = (r : UnitAddCircle)) :
    Int.fract x = r := by
  have hfract : Int.fract x ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa only [zero_add] using
      (show Int.fract x ∈ Set.Ico (0 : ℝ) 1 from
        ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩)
  have hr' : r ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa only [zero_add] using hr
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (p := (1 : ℝ)) (a := 0) hfract hr').mp
  exact (AddCircle.coe_fract x).trans h

noncomputable def bkr_fract_shift_into_middle
    (A X : ℝ) (hA : A ∈ Set.Ioo (0 : ℝ) 1)
    (hX : X ∈ Set.Ico (0 : ℝ) 1) :
    X ∈ Set.Ioo ((min A (1 - A)) / 4)
        (1 - (min A (1 - A)) / 4) ∨
      Int.fract (X + A) ∈ Set.Ioo ((min A (1 - A)) / 4)
        (1 - (min A (1 - A)) / 4) := by
  rcases hA with ⟨hA0, hA1⟩
  rcases hX with ⟨hX0, hX1⟩
  let d : ℝ := min A (1 - A)
  have hdA : d ≤ A := by
    exact min_le_left A (1 - A)
  have hdOneA : d ≤ 1 - A := by
    exact min_le_right A (1 - A)
  have hd0 : 0 < d := by
    dsimp only [d]
    exact lt_min hA0 (sub_pos.mpr hA1)
  change X ∈ Set.Ioo (d / 4) (1 - d / 4) ∨
    Int.fract (X + A) ∈ Set.Ioo (d / 4) (1 - d / 4)
  by_cases hmid : X ∈ Set.Ioo (d / 4) (1 - d / 4)
  · exact Or.inl hmid
  right
  by_cases hlow : X ≤ d / 4
  · have hY0 : 0 ≤ X + A := by linarith
    have hY1 : X + A < 1 := by linarith
    have hfract : Int.fract (X + A) = X + A :=
      Int.fract_eq_self.mpr ⟨hY0, hY1⟩
    rw [hfract]
    constructor <;> linarith
  · have hXlow : d / 4 < X := lt_of_not_ge hlow
    have hXhigh : 1 - d / 4 ≤ X := by
      by_contra hnot
      exact hmid ⟨hXlow, lt_of_not_ge hnot⟩
    have hY0 : 0 ≤ X + A - 1 := by linarith
    have hY1 : X + A - 1 < 1 := by linarith
    have hfractSub : Int.fract (X + A - 1) = X + A - 1 :=
      Int.fract_eq_self.mpr ⟨hY0, hY1⟩
    have hfract : Int.fract (X + A) = X + A - 1 := by
      rw [← Int.fract_sub_one (X + A)]
      exact hfractSub
    rw [hfract]
    constructor <;> linarith

noncomputable def bkr_localAdditiveExtensionIndex_pos_small
    (δ x : ℝ) (hδ : 0 < δ) :
    0 < bkrLocalAdditiveExtensionIndex δ x ∧
      |x / (bkrLocalAdditiveExtensionIndex δ x : ℝ)| < δ := by
  unfold bkrLocalAdditiveExtensionIndex
  constructor
  · omega
  · have hceil :
        |x| / δ ≤ (Nat.ceil (|x| / δ) : ℝ) :=
      Nat.le_ceil (|x| / δ)
    have hlt :
        |x| / δ < ((Nat.ceil (|x| / δ) + 1 : ℕ) : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith
    have hnpos :
        0 < ((Nat.ceil (|x| / δ) + 1 : ℕ) : ℝ) := by
      positivity
    rw [abs_div, abs_of_pos hnpos]
    apply (div_lt_iff₀ hnpos).2
    have hmul := (div_lt_iff₀ hδ).1 hlt
    nlinarith

noncomputable def
    bkr_circle_endomorphism_localExtension_coe
    (φ : UnitAddCircle →ₜ+ UnitAddCircle)
    (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    (bkrLocalAdditiveExtension
        (bkrCircleEndomorphismRepresentative φ) δ x : UnitAddCircle) =
      φ (x : UnitAddCircle) := by
  let n := bkrLocalAdditiveExtensionIndex δ x
  have hnpos : 0 < n :=
    (bkr_localAdditiveExtensionIndex_pos_small δ x hδ).1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  unfold bkrLocalAdditiveExtension
  change ((((n : ℝ) *
      bkrCircleEndomorphismRepresentative φ (x / (n : ℝ))) : ℝ) :
        UnitAddCircle) = φ (x : UnitAddCircle)
  calc
    ((((n : ℝ) *
        bkrCircleEndomorphismRepresentative φ (x / (n : ℝ))) : ℝ) :
          UnitAddCircle) =
        ((n • bkrCircleEndomorphismRepresentative φ
          (x / (n : ℝ)) : ℝ) : UnitAddCircle) := by
      congr 1
      simp only [nsmul_eq_mul]
    _ = n • (bkrCircleEndomorphismRepresentative φ
          (x / (n : ℝ)) : UnitAddCircle) :=
      AddCircle.coe_nsmul (1 : ℝ)
    _ = n • φ ((x / (n : ℝ) : ℝ) : UnitAddCircle) := by
      rw [bkrCircleEndomorphismRepresentative_coe]
    _ = φ (n • ((x / (n : ℝ) : ℝ) : UnitAddCircle)) := by
      rw [map_nsmul]
    _ = φ (x : UnitAddCircle) := by
      congr 1
      rw [← AddCircle.coe_nsmul]
      congr 1
      simp only [nsmul_eq_mul]
      field_simp

open Filter Topology in
noncomputable def
    bkr_circle_endomorphism_localExtension_eq_scaled
    (φ : UnitAddCircle →ₜ+ UnitAddCircle)
    (δ : ℝ) (hδ : 0 < δ)
    (hadd : ∀ (x y : ℝ), |x| < δ → |y| < δ → |x + y| < δ →
      bkrCircleEndomorphismRepresentative φ (x + y) =
        bkrCircleEndomorphismRepresentative φ x +
          bkrCircleEndomorphismRepresentative φ y)
    (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : |x / (n : ℝ)| < δ) :
    bkrLocalAdditiveExtension
        (bkrCircleEndomorphismRepresentative φ) δ x =
      (n : ℝ) *
        bkrCircleEndomorphismRepresentative φ (x / (n : ℝ)) := by
  let N := bkrLocalAdditiveExtensionIndex δ x
  have hN := bkr_localAdditiveExtensionIndex_pos_small δ x hδ
  have hNpos : 0 < N := hN.1
  have hNsmall : |x / (N : ℝ)| < δ := hN.2
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  let t : ℝ := x / ((N : ℝ) * (n : ℝ))
  have hnt : (n : ℝ) * t = x / (N : ℝ) := by
    dsimp only [t]
    field_simp
  have hNt : (N : ℝ) * t = x / (n : ℝ) := by
    dsimp only [t]
    field_simp
  have hnscale :=
    bkr_circle_endomorphism_representative_nat_mul
      φ δ hδ hadd n t (by rw [hnt]; exact hNsmall)
  have hNscale :=
    bkr_circle_endomorphism_representative_nat_mul
      φ δ hδ hadd N t (by rw [hNt]; exact hx)
  rw [hnt] at hnscale
  rw [hNt] at hNscale
  unfold bkrLocalAdditiveExtension
  change (N : ℝ) *
      bkrCircleEndomorphismRepresentative φ (x / (N : ℝ)) = _
  rw [hnscale, hNscale]
  ring

open Filter Topology in
noncomputable def
    bkr_circle_endomorphism_localExtension_add
    (φ : UnitAddCircle →ₜ+ UnitAddCircle)
    (δ : ℝ) (hδ : 0 < δ)
    (hadd : ∀ (x y : ℝ), |x| < δ → |y| < δ → |x + y| < δ →
      bkrCircleEndomorphismRepresentative φ (x + y) =
        bkrCircleEndomorphismRepresentative φ x +
          bkrCircleEndomorphismRepresentative φ y) :
    ∀ x y : ℝ,
      bkrLocalAdditiveExtension
          (bkrCircleEndomorphismRepresentative φ) δ (x + y) =
        bkrLocalAdditiveExtension
            (bkrCircleEndomorphismRepresentative φ) δ x +
          bkrLocalAdditiveExtension
            (bkrCircleEndomorphismRepresentative φ) δ y := by
  intro x y
  let n := bkrLocalAdditiveExtensionIndex δ (|x| + |y|)
  have hn :=
    bkr_localAdditiveExtensionIndex_pos_small δ (|x| + |y|) hδ
  have hnpos : 0 < n := hn.1
  have hnRpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hbase : (|x| + |y|) / (n : ℝ) < δ := by
    have hnsmall := hn.2
    change |(|x| + |y|) / (n : ℝ)| < δ at hnsmall
    have hs0 : 0 ≤ |x| + |y| := by positivity
    rw [abs_div, abs_of_nonneg hs0, abs_of_pos hnRpos] at hnsmall
    exact hnsmall
  have hxsmall : |x / (n : ℝ)| < δ := by
    rw [abs_div, abs_of_pos hnRpos]
    exact (div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (abs_nonneg y)) hnRpos.le).trans_lt hbase
  have hysmall : |y / (n : ℝ)| < δ := by
    rw [abs_div, abs_of_pos hnRpos]
    exact (div_le_div_of_nonneg_right
      (le_add_of_nonneg_left (abs_nonneg x)) hnRpos.le).trans_lt hbase
  have hxysmall : |(x + y) / (n : ℝ)| < δ := by
    rw [abs_div, abs_of_pos hnRpos]
    exact (div_le_div_of_nonneg_right (abs_add_le x y) hnRpos.le).trans_lt hbase
  have hsum := bkr_circle_endomorphism_localExtension_eq_scaled
    φ δ hδ hadd n hnpos (x + y) hxysmall
  have hx := bkr_circle_endomorphism_localExtension_eq_scaled
    φ δ hδ hadd n hnpos x hxsmall
  have hy := bkr_circle_endomorphism_localExtension_eq_scaled
    φ δ hδ hadd n hnpos y hysmall
  have hlocal := hadd (x / (n : ℝ)) (y / (n : ℝ))
    hxsmall hysmall (by
      rw [← add_div]
      exact hxysmall)
  rw [hsum, hx, hy]
  rw [show (x + y) / (n : ℝ) =
    x / (n : ℝ) + y / (n : ℝ) by ring]
  rw [hlocal]
  ring

open Filter Topology in
noncomputable def
    bkr_circle_endomorphism_localExtension_eq_local
    (φ : UnitAddCircle →ₜ+ UnitAddCircle)
    (δ : ℝ) (hδ : 0 < δ)
    (hadd : ∀ (x y : ℝ), |x| < δ → |y| < δ → |x + y| < δ →
      bkrCircleEndomorphismRepresentative φ (x + y) =
        bkrCircleEndomorphismRepresentative φ x +
          bkrCircleEndomorphismRepresentative φ y)
    (x : ℝ) (hx : |x| < δ) :
    bkrLocalAdditiveExtension
        (bkrCircleEndomorphismRepresentative φ) δ x =
      bkrCircleEndomorphismRepresentative φ x := by
  simpa only [Nat.cast_one, div_one, one_mul] using
    (bkr_circle_endomorphism_localExtension_eq_scaled
      φ δ hδ hadd 1 Nat.zero_lt_one x
      (by simpa only [Nat.cast_one, div_one] using hx))

open Filter Topology in
noncomputable def
    bkr_circle_endomorphism_localExtension_continuousAt_zero
    (φ : UnitAddCircle →ₜ+ UnitAddCircle)
    (δ : ℝ) (hδ : 0 < δ)
    (hadd : ∀ (x y : ℝ), |x| < δ → |y| < δ → |x + y| < δ →
      bkrCircleEndomorphismRepresentative φ (x + y) =
        bkrCircleEndomorphismRepresentative φ x +
          bkrCircleEndomorphismRepresentative φ y) :
    ContinuousAt
      (bkrLocalAdditiveExtension
        (bkrCircleEndomorphismRepresentative φ) δ) 0 := by
  apply (bkrCircleEndomorphismRepresentative_continuousAt_zero φ).congr_of_eventuallyEq
  filter_upwards [eventually_abs_sub_lt (0 : ℝ) hδ] with x hx
  apply bkr_circle_endomorphism_localExtension_eq_local φ δ hδ hadd
  simpa only [sub_zero] using hx

open Filter Topology in
noncomputable def
    bkr_continuousAddCircleEndomorphism_additive_lift
    (φ : UnitAddCircle →ₜ+ UnitAddCircle) :
    ∃ F : ℝ →+ ℝ, Continuous F ∧
      ∀ x : ℝ, (F x : UnitAddCircle) = φ (x : UnitAddCircle) := by
  obtain ⟨δ, hδ, hadd⟩ :=
    bkr_circle_endomorphism_representative_locally_additive φ
  let F : ℝ →+ ℝ := AddMonoidHom.mk'
    (bkrLocalAdditiveExtension
      (bkrCircleEndomorphismRepresentative φ) δ)
    (bkr_circle_endomorphism_localExtension_add φ δ hδ hadd)
  have hF0 : ContinuousAt F 0 := by
    change ContinuousAt
      (bkrLocalAdditiveExtension
        (bkrCircleEndomorphismRepresentative φ) δ) 0
    exact bkr_circle_endomorphism_localExtension_continuousAt_zero
      φ δ hδ hadd
  have hF : Continuous F :=
    continuous_of_continuousAt_zero F hF0
  refine ⟨F, hF, fun x => ?_⟩
  change (bkrLocalAdditiveExtension
      (bkrCircleEndomorphismRepresentative φ) δ x : UnitAddCircle) =
    φ (x : UnitAddCircle)
  exact bkr_circle_endomorphism_localExtension_coe φ δ hδ x

open Filter Topology in
noncomputable def
    bkr_continuousAddCircleEndomorphism_on_coe_eq_zsmul
    (φ : UnitAddCircle →ₜ+ UnitAddCircle) :
    ∃ k : ℤ, ∀ x : ℝ,
      φ (x : UnitAddCircle) = k • (x : UnitAddCircle) := by
  obtain ⟨F, hF, hlift⟩ :=
    bkr_continuousAddCircleEndomorphism_additive_lift φ
  have hlinear : ∀ x : ℝ, F x = x * F 1 := by
    intro x
    simpa only [smul_eq_mul, mul_one] using
      (map_real_smul F hF x (1 : ℝ))
  have hF1 : (F 1 : UnitAddCircle) = 0 := by
    calc
      (F 1 : UnitAddCircle) =
          φ (((1 : ℝ) : UnitAddCircle)) := hlift 1
      _ = φ 0 := by rw [AddCircle.coe_period]
      _ = 0 := map_zero φ
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hF1
  have hk' : (k : ℝ) = F 1 := by
    simpa only [zsmul_eq_mul, mul_one] using hk
  refine ⟨k, fun x => ?_⟩
  calc
    φ (x : UnitAddCircle) = (F x : UnitAddCircle) := (hlift x).symm
    _ = ((x * F 1 : ℝ) : UnitAddCircle) := by rw [hlinear]
    _ = ((x * (k : ℝ) : ℝ) : UnitAddCircle) := by rw [hk']
    _ = (((k : ℝ) * x : ℝ) : UnitAddCircle) := by ring
    _ = ((k • x : ℝ) : UnitAddCircle) := by
      congr 1
      simp only [zsmul_eq_mul]
    _ = k • (x : UnitAddCircle) := AddCircle.coe_zsmul (1 : ℝ)

def bkr_mapClusterPt_atTop_zsmul_iff_nsmul
    {G : Type} [SubNegMonoid G] [TopologicalSpace G] {x y : G} :
    MapClusterPt x Filter.atTop (fun n : ℤ => n • y) ↔
      MapClusterPt x Filter.atTop (fun n : ℕ => n • y) := by
  simp_rw [MapClusterPt, ← Nat.map_cast_int_atTop, Filter.map_map,
    Function.comp_def, natCast_zsmul]

open Filter Function Set in
open scoped Topology in
def bkr_mapClusterPt_self_zsmul_atTop_nsmul
    {G : Type} [AddGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (x : G) (m : ℤ) :
    MapClusterPt (m • x) Filter.atTop (fun n : ℕ => n • x) := by
  obtain ⟨y, hy⟩ :
      ∃ y, MapClusterPt y Filter.atTop (fun n : ℤ => n • x) :=
    exists_clusterPt_of_compactSpace _
  rw [← bkr_mapClusterPt_atTop_zsmul_iff_nsmul]
  have H :
      MapClusterPt (m • x) (Filter.atTop.curry Filter.atTop)
        ↿(fun a b : ℤ => (m + b - a) • x) := by
    have hcont :
        ContinuousAt (fun yz : G × G => m • x + yz.2 - yz.1) (y, y) := by
      fun_prop
    simpa only [Function.comp_def, sub_zsmul, add_zsmul, neg_zsmul,
      Prod.map, sub_eq_add_neg, add_neg_cancel_right] using!
        (hy.curry_prodMap hy).continuousAt_comp hcont
  suffices Filter.Tendsto ↿(fun a b : ℤ => m + b - a)
      (Filter.atTop.curry Filter.atTop) Filter.atTop from H.of_comp this
  refine Filter.Tendsto.curry <| .of_forall fun a => ?_
  simp only [sub_eq_add_neg]
  exact tendsto_atTop_add_const_right _ _
    (tendsto_atTop_add_const_left Filter.atTop m tendsto_id)

open Filter Function Set in
open scoped Topology in
def bkr_mapClusterPt_atTop_nsmul_tfae
    {G : Type} [AddGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (x y : G) :
    List.TFAE [
      MapClusterPt x Filter.atTop (fun n : ℕ => n • y),
      MapClusterPt x Filter.atTop (fun n : ℤ => n • y),
      x ∈ closure (Set.range fun n : ℕ => n • y),
      x ∈ closure (Set.range fun n : ℤ => n • y)] := by
  tfae_have 2 ↔ 1 := bkr_mapClusterPt_atTop_zsmul_iff_nsmul
  tfae_have 3 → 4 := by
    refine fun h => closure_mono (Set.range_subset_iff.2 fun n => ?_) h
    exact ⟨(n : ℤ), natCast_zsmul y n⟩
  tfae_have 4 → 1 := by
    refine fun h => closure_minimal ?_ isClosed_setOf_clusterPt h
    exact Set.range_subset_iff.2 (bkr_mapClusterPt_self_zsmul_atTop_nsmul y)
  tfae_have 1 → 3 := by
    rw [mem_closure_iff_clusterPt]
    exact (ClusterPt.mono · (le_principal_iff.2 Filter.range_mem_map))
  tfae_finish

open Filter Function Set in
open scoped Topology in
def bkr_closure_range_zsmul_eq_nsmul
    {G : Type} [AddGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (x : G) :
    closure (Set.range fun n : ℤ => n • x) =
      closure (Set.range fun n : ℕ => n • x) := by
  ext y
  exact (bkr_mapClusterPt_atTop_nsmul_tfae y x).out 3 2

open Filter Function Set in
open scoped Topology in
def bkr_denseRange_nsmul_arbitrarily_late_hit
    {G : Type} [AddGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (x : G)
    (hdense : DenseRange (fun n : ℕ => n • x))
    {U : Set G} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ m • x ∈ U := by
  obtain ⟨z, hzU⟩ := hUne
  have hzcl : z ∈ closure (Set.range fun n : ℕ => n • x) := by
    rw [hdense.closure_range]
    exact Set.mem_univ z
  have hcluster :
      MapClusterPt z Filter.atTop (fun n : ℕ => n • x) :=
    ((bkr_mapClusterPt_atTop_nsmul_tfae z x).out 2 0).mp hzcl
  have hfreq : ∃ᶠ n : ℕ in Filter.atTop, n • x ∈ U :=
    hcluster.frequently (hUopen.mem_nhds hzU)
  exact Filter.frequently_atTop'.mp hfreq

open Filter Function Set in
open scoped Topology in
def bkr_denseRange_zsmul_iff_nsmul
    {G : Type} [AddGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] {x : G} :
    DenseRange (fun n : ℤ => n • x) ↔
      DenseRange (fun n : ℕ => n • x) := by
  simp only [DenseRange, dense_iff_closure_eq,
    bkr_closure_range_zsmul_eq_nsmul]

open Filter Function Set in
open scoped Topology in
noncomputable def bkr_addCircle_denseRange_nsmul_of_irrational
    (γ : ℝ) (hγ : Irrational γ) :
    DenseRange (fun n : ℕ => n • (γ : AddCircle (1 : ℝ))) := by
  rw [← bkr_denseRange_zsmul_iff_nsmul]
  exact bkr_addCircle_denseRange_zsmul_of_irrational γ hγ

open Filter Function Set in
open scoped Topology in
noncomputable def bkr_irrational_rotation_hits_fract_interval
    (γ a b : ℝ) (hγ : Irrational γ) (ha0 : 0 < a)
    (hab : a < b) (hb1 : b < 1) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧
      Int.fract (γ * (m : ℝ)) ∈ Set.Ioo a b := by
  intro N
  obtain ⟨m, hm, hmem⟩ :=
    bkr_denseRange_nsmul_arbitrarily_late_hit
      (γ : AddCircle (1 : ℝ))
      (bkr_addCircle_denseRange_nsmul_of_irrational γ hγ)
      (bkrAddCircleInterval_isOpen a b ha0 hab hb1)
      (bkrAddCircleInterval_nonempty a b ha0.le hab hb1.le) N
  exact ⟨m, hm,
    (bkrAddCircleInterval_nsmul_mem_iff γ a b m).mp hmem⟩

def bkr_orbitClosure_mem_closure_range
    (α β : ℝ) (z : UnitAddCircle × UnitAddCircle) :
    z ∈ bkrOrbitClosure α β ↔
      z ∈ closure (Set.range fun n : ℤ =>
        n • ((α : UnitAddCircle), (β : UnitAddCircle))) := by
  unfold bkrOrbitClosure
  change z ∈
      (↑((AddSubgroup.zmultiples
        ((α : UnitAddCircle), (β : UnitAddCircle))).topologicalClosure) :
        Set (UnitAddCircle × UnitAddCircle)) ↔ _
  rw [AddSubgroup.topologicalClosure_coe,
    AddSubgroup.coe_zmultiples]

noncomputable def bkr_orbitSnd_injective_of_horizontalKernel_eq_bot
    (α β : ℝ) (hK : bkrHorizontalKernel α β = ⊥) :
    Function.Injective (bkrOrbitSnd α β) := by
  intro x y hxy
  have hsecond : x.1.2 = y.1.2 := by
    simpa only [bkrOrbitSnd_apply] using hxy
  have hkernel : x.1.1 - y.1.1 ∈ bkrHorizontalKernel α β := by
    rw [bkrHorizontalKernel_mem_iff]
    have hsub : x.1 - y.1 ∈ bkrOrbitClosure α β :=
      (bkrOrbitClosure α β).sub_mem x.2 y.2
    convert hsub using 1
    ext
    · rfl
    · change (0 : UnitAddCircle) = x.1.2 - y.1.2
      rw [hsecond, sub_self]
  rw [hK] at hkernel
  have hfirst : x.1.1 = y.1.1 := by
    have hz : x.1.1 - y.1.1 = 0 := by
      simpa only [AddSubgroup.mem_bot] using hkernel
    exact sub_eq_zero.mp hz
  apply Subtype.ext
  exact Prod.ext hfirst hsecond

noncomputable def bkr_orbitSnd_surjective
    (α β : ℝ) (hβirr : Irrational β) :
    Function.Surjective (bkrOrbitSnd α β) := by
  have hcompact :
      IsCompact (Set.range (bkrOrbitSnd α β)) :=
    isCompact_range
      (ContinuousAddMonoidHom.continuous_toFun (bkrOrbitSnd α β))
  have hclosed : IsClosed (Set.range (bkrOrbitSnd α β)) :=
    hcompact.isClosed
  have hsubset :
      Set.range (fun n : ℤ => n • (β : UnitAddCircle)) ⊆
        Set.range (bkrOrbitSnd α β) := by
    rintro y ⟨n, rfl⟩
    let x : UnitAddCircle × UnitAddCircle :=
      ((α : UnitAddCircle), (β : UnitAddCircle))
    have hzm : n • x ∈ AddSubgroup.zmultiples x :=
      AddSubgroup.zsmul_mem_zmultiples x n
    have hcl : n • x ∈ bkrOrbitClosure α β :=
      AddSubgroup.le_topologicalClosure _ hzm
    refine ⟨⟨n • x, hcl⟩, ?_⟩
    rw [bkrOrbitSnd_apply]
    rfl
  have hdense :
      DenseRange (fun n : ℤ => n • (β : UnitAddCircle)) :=
    bkr_addCircle_denseRange_zsmul_of_irrational β hβirr
  have hclosure :
      closure (Set.range (fun n : ℤ => n • (β : UnitAddCircle))) =
        Set.univ := hdense.closure_range
  have hfull : Set.univ ⊆ Set.range (bkrOrbitSnd α β) := by
    rw [← hclosure]
    exact closure_minimal hsubset hclosed
  intro y
  exact hfull (Set.mem_univ y)

noncomputable def bkrOrbitSndEquiv
    (α β : ℝ) (hβirr : Irrational β)
    (hK : bkrHorizontalKernel α β = ⊥) :
    bkrOrbitClosureClosed α β ≃ₜ+ UnitAddCircle := by
  let hf : Function.Bijective (bkrOrbitSnd α β) :=
    ⟨bkr_orbitSnd_injective_of_horizontalKernel_eq_bot α β hK,
      bkr_orbitSnd_surjective α β hβirr⟩
  let e : bkrOrbitClosureClosed α β ≃+ UnitAddCircle :=
    AddEquiv.ofBijective (bkrOrbitSnd α β) hf
  have he : Continuous e := by
    change Continuous (bkrOrbitSnd α β)
    exact ContinuousAddMonoidHom.continuous_toFun (bkrOrbitSnd α β)
  have heinv : Continuous e.symm :=
    Continuous.continuous_symm_of_equiv_compact_to_t2 he
  exact ContinuousAddEquiv.mk e he heinv

noncomputable def bkrOrbitSndEquiv_symm_beta
    (α β : ℝ) (hβirr : Irrational β)
    (hK : bkrHorizontalKernel α β = ⊥) :
    (bkrOrbitSndEquiv α β hβirr hK).symm (β : UnitAddCircle) =
      bkrOrbitGenerator α β := by
  apply (bkrOrbitSndEquiv α β hβirr hK).injective
  rw [(bkrOrbitSndEquiv α β hβirr hK).apply_symm_apply]
  change (β : UnitAddCircle) = bkrOrbitSnd α β (bkrOrbitGenerator α β)
  rw [bkrOrbitSnd_apply, bkrOrbitGenerator_snd]

open Filter Topology in
noncomputable def
    bkr_circle_relation_of_horizontalKernel_eq_bot
    (α β : ℝ) (hβirr : Irrational β)
    (hK : bkrHorizontalKernel α β = ⊥) :
    ∃ k : ℤ, (α : UnitAddCircle) = k • (β : UnitAddCircle) := by
  let φ : UnitAddCircle →ₜ+ UnitAddCircle :=
    (bkrOrbitFst α β).comp
      ((bkrOrbitSndEquiv α β hβirr hK).symm :
        UnitAddCircle →ₜ+ bkrOrbitClosureClosed α β)
  obtain ⟨k, hk⟩ :=
    bkr_continuousAddCircleEndomorphism_on_coe_eq_zsmul φ
  refine ⟨k, ?_⟩
  have h := hk β
  change bkrOrbitFst α β
      ((bkrOrbitSndEquiv α β hβirr hK).symm
        (β : UnitAddCircle)) =
    k • (β : UnitAddCircle) at h
  rw [bkrOrbitSndEquiv_symm_beta,
    bkrOrbitFst_apply, bkrOrbitGenerator_fst] at h
  exact h

noncomputable def
    bkr_exists_middle_rectangle_point_of_horizontalKernel_ne_bot
    (α β : ℝ) (hβirr : Irrational β)
    (hK : bkrHorizontalKernel α β ≠ ⊥) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧
      ∃ z : UnitAddCircle × UnitAddCircle,
        z ∈ closure (Set.range fun n : ℤ =>
          n • ((α : UnitAddCircle), (β : UnitAddCircle))) ∧
        z.1 ∈ bkrAddCircleInterval (d / 4) (1 - d / 4) ∧
        z.2 ∈ bkrAddCircleInterval (1 - d / 16) (1 - d / 64) := by
  obtain ⟨a, ha0⟩ :=
    AddSubgroup.ne_bot_iff_exists_ne_zero.mp hK
  let A : ℝ :=
    ((AddCircle.equivIco (1 : ℝ) 0 a.1 : _) : ℝ)
  have hAIco : A ∈ Set.Ico (0 : ℝ) 1 := by
    dsimp only [A]
    simpa only [zero_add] using
      (AddCircle.equivIco (1 : ℝ) 0 a.1).property
  have haCoe : (A : UnitAddCircle) = a.1 := by
    dsimp only [A]
    change (AddCircle.equivIco (1 : ℝ) 0).symm
      (AddCircle.equivIco (1 : ℝ) 0 a.1) = a.1
    exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply a.1
  have hAne : A ≠ 0 := by
    intro hA
    rw [hA] at haCoe
    have haValZero : a.1 = (0 : UnitAddCircle) := by
      rw [← haCoe]
      exact AddCircle.coe_zero (1 : ℝ)
    exact ha0 (Subtype.ext haValZero)
  have hApos : 0 < A :=
    lt_of_le_of_ne hAIco.1 hAne.symm
  have hAlt : A < 1 := hAIco.2
  let d : ℝ := min A (1 - A)
  have hdA : d ≤ A := min_le_left A (1 - A)
  have hdOneA : d ≤ 1 - A := min_le_right A (1 - A)
  have hd0 : 0 < d := by
    dsimp only [d]
    exact lt_min hApos (sub_pos.mpr hAlt)
  have hdhalf : d ≤ 1 / 2 := by
    nlinarith
  let y : UnitAddCircle := ((1 - d / 32 : ℝ) : UnitAddCircle)
  obtain ⟨z0, hz0⟩ :=
    bkr_orbitSnd_surjective α β hβirr y
  have hz0snd : z0.1.2 = y := by
    simpa only [bkrOrbitSnd_apply] using hz0
  have hyIco : 1 - d / 32 ∈ Set.Ico (0 : ℝ) 1 := by
    constructor <;> nlinarith
  have hyIco' : 1 - d / 32 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
    simpa only [zero_add] using hyIco
  have hz0sndInterval :
      z0.1.2 ∈ bkrAddCircleInterval
        (1 - d / 16) (1 - d / 64) := by
    unfold bkrAddCircleInterval
    simp only [Set.mem_setOf_eq]
    rw [hz0snd]
    dsimp only [y]
    rw [AddCircle.equivIco_coe_eq hyIco']
    constructor <;> nlinarith
  let X : ℝ :=
    ((AddCircle.equivIco (1 : ℝ) 0 z0.1.1 : _) : ℝ)
  have hXIco : X ∈ Set.Ico (0 : ℝ) 1 := by
    dsimp only [X]
    simpa only [zero_add] using
      (AddCircle.equivIco (1 : ℝ) 0 z0.1.1).property
  have hz0fstCoe : (X : UnitAddCircle) = z0.1.1 := by
    dsimp only [X]
    change (AddCircle.equivIco (1 : ℝ) 0).symm
      (AddCircle.equivIco (1 : ℝ) 0 z0.1.1) = z0.1.1
    exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z0.1.1
  rcases bkr_fract_shift_into_middle A X
    ⟨hApos, hAlt⟩ hXIco with hmid | hshift
  · have hmid' : X ∈ Set.Ioo (d / 4) (1 - d / 4) := by
      simpa only [d] using hmid
    refine ⟨d, hd0, hdhalf, z0.1, ?_, ?_, hz0sndInterval⟩
    · exact (bkr_orbitClosure_mem_closure_range α β z0.1).mp z0.2
    · unfold bkrAddCircleInterval
      change X ∈ Set.Ioo (d / 4) (1 - d / 4)
      exact hmid'
  · have hshift' :
        Int.fract (X + A) ∈ Set.Ioo (d / 4) (1 - d / 4) := by
      simpa only [d] using hshift
    let z : UnitAddCircle × UnitAddCircle := z0.1 + (a.1, 0)
    have haMem : (a.1, 0) ∈ bkrOrbitClosure α β :=
      (bkrHorizontalKernel_mem_iff α β a.1).mp a.2
    have hzMem : z ∈ bkrOrbitClosure α β :=
      (bkrOrbitClosure α β).add_mem z0.2 haMem
    have hzfst : z.1 = ((X + A : ℝ) : UnitAddCircle) := by
      dsimp only [z]
      change z0.1.1 + a.1 = ((X + A : ℝ) : UnitAddCircle)
      rw [← hz0fstCoe, ← haCoe]
      exact (AddCircle.coe_add (1 : ℝ) X A).symm
    have hzfstInterval :
        z.1 ∈ bkrAddCircleInterval (d / 4) (1 - d / 4) := by
      rw [hzfst]
      exact (bkrAddCircleInterval_coe_mem_iff
        (X + A) (d / 4) (1 - d / 4)).mpr hshift'
    have hzsndInterval :
        z.2 ∈ bkrAddCircleInterval
          (1 - d / 16) (1 - d / 64) := by
      simpa only [z, Prod.snd_add, add_zero] using hz0sndInterval
    refine ⟨d, hd0, hdhalf, z, ?_, hzfstInterval, hzsndInterval⟩
    exact (bkr_orbitClosure_mem_closure_range α β z).mp hzMem

noncomputable def bkr_parameter_sequence_of_unbounded_windows
    (α β ε : ℝ) (m₀ : ℕ)
    (hhit : ∀ N : ℕ, ∃ m : ℕ,
      N < m ∧ bkrGoodRoundingWindow α β ε m)
    (hbridge : ∀ m : ℕ, m₀ ≤ m →
      bkrGoodRoundingWindow α β ε m →
      bkrLooseParameters α β m
        (Nat.ceil (α * (m : ℝ)) - 1)
        (Nat.ceil (β * (m : ℝ)))) :
    ∃ ms u v : ℕ → ℕ, StrictMono ms ∧
      ∀ i, bkrLooseParameters α β (ms i) (u i) (v i) := by
  let P : ℕ → Prop := fun m =>
    m₀ ≤ m ∧ bkrGoodRoundingWindow α β ε m
  have hP : ∀ N : ℕ, ∃ m : ℕ, N < m ∧ P m := by
    intro N
    obtain ⟨m, hm, hgood⟩ := hhit (max N m₀)
    refine ⟨m, lt_of_le_of_lt (Nat.le_max_left N m₀) hm, ?_, hgood⟩
    exact le_of_lt (lt_of_le_of_lt (Nat.le_max_right N m₀) hm)
  obtain ⟨ms, hms, hmsP⟩ := Nat.exists_strictMono_subsequence hP
  let u : ℕ → ℕ := fun i => Nat.ceil (α * (ms i : ℝ)) - 1
  let v : ℕ → ℕ := fun i => Nat.ceil (β * (ms i : ℝ))
  refine ⟨ms, u, v, hms, ?_⟩
  intro i
  exact hbridge (ms i) (hmsP i).1 (hmsP i).2

noncomputable def bkr_profile_exponent_identity
    (m u v : ℕ) (huv : u < v) (hvm : v ≤ m)
    (hsize : v ^ 2 ≤ (u + 1) * m) :
    m * (v - u - 1) + ((u + 1) * m - v ^ 2) =
      v * (m - v) := by
  have hsplit : v - u - 1 + (u + 1) = v := by omega
  calc
    m * (v - u - 1) + ((u + 1) * m - v ^ 2) =
        (m * (v - u - 1) + (u + 1) * m) - v ^ 2 := by
      rw [add_tsub_assoc_of_le hsize]
    _ = m * (v - u - 1 + (u + 1)) - v ^ 2 := by ring
    _ = m * v - v ^ 2 := by rw [hsplit]
    _ = v * (m - v) := by
      rw [pow_two, mul_tsub, Nat.mul_comm m v]

def bkr_radius_floor_eq (v m : ℕ) (hvm : v ≤ m) :
    Nat.floor ((1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m) * (2 : ℝ) ^ m) =
      2 ^ m - 2 ^ v := by
  have hpow : 2 ^ v ≤ 2 ^ m :=
    pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hvm
  have hcalc :
      (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m) * (2 : ℝ) ^ m =
        ((2 ^ m - 2 ^ v : ℕ) : ℝ) := by
    calc
      (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m) * (2 : ℝ) ^ m =
          (2 : ℝ) ^ m - (2 : ℝ) ^ v := by
        field_simp
      _ = ((2 ^ m - 2 ^ v : ℕ) : ℝ) := by
        rw [Nat.cast_sub hpow]
        norm_num only [Nat.cast_ofNat, Nat.cast_pow]
  rw [hcalc, Nat.floor_natCast]

def bkr_radius_nonneg (v m : ℕ) (hvm : v ≤ m) :
    0 ≤ 1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m := by
  have hpow_nat : 2 ^ v ≤ 2 ^ m :=
    pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hvm
  have hpow_real : (2 : ℝ) ^ v ≤ (2 : ℝ) ^ m := by
    exact_mod_cast hpow_nat
  apply sub_nonneg.mpr
  exact (div_le_one₀ (by positivity)).mpr hpow_real

noncomputable def bkr_radius_of_ceil (β : ℝ) (m : ℕ) :
    1 - (2 : ℝ) ^ (Nat.ceil (β * (m : ℝ))) / (2 : ℝ) ^ m ≤
      1 - (((2 ^ m : ℕ) : ℝ) ^ (β - 1)) := by
  have hceil : β * (m : ℝ) ≤ (Nat.ceil (β * (m : ℝ)) : ℝ) :=
    Nat.le_ceil (β * (m : ℝ))
  have hpow :
      (2 : ℝ) ^ (β * (m : ℝ)) ≤
        (2 : ℝ) ^ (Nat.ceil (β * (m : ℝ))) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
  have hdiv :
      (2 : ℝ) ^ (β * (m : ℝ)) / (2 : ℝ) ^ m ≤
        (2 : ℝ) ^ (Nat.ceil (β * (m : ℝ))) / (2 : ℝ) ^ m := by
    exact div_le_div_of_nonneg_right hpow (by positivity)
  have hrhs :
      (((2 ^ m : ℕ) : ℝ) ^ (β - 1)) =
        (2 : ℝ) ^ (β * (m : ℝ)) / (2 : ℝ) ^ m := by
    calc
      (((2 ^ m : ℕ) : ℝ) ^ (β - 1)) =
          (((2 : ℝ) ^ m) ^ (β - 1)) := by
        norm_num only [Nat.cast_ofNat, Nat.cast_pow]
      _ = (((2 : ℝ) ^ (m : ℝ)) ^ (β - 1)) := by
        rw [Real.rpow_natCast]
      _ = (2 : ℝ) ^ ((m : ℝ) * (β - 1)) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (β * (m : ℝ) - (m : ℝ)) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ (β * (m : ℝ)) / (2 : ℝ) ^ m := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  rw [hrhs]
  linarith

noncomputable def bkr_rational_has_denominator_multiple
    (x : ℝ) (hx : ¬ Irrational x) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : ℤ, x * (D : ℝ) = (z : ℝ) := by
  obtain ⟨q, rfl⟩ := exists_rat_of_not_irrational hx
  refine ⟨q.den, Nat.pos_of_ne_zero q.den_ne_zero, q.num, ?_⟩
  exact_mod_cast Rat.mul_den_eq_num q

noncomputable def bkr_rounding_exponent_identity
    (α β : ℝ) (m : ℕ) :
    (m : ℝ) * (Nat.ceil (α * (m : ℝ)) : ℝ) -
        (Nat.ceil (β * (m : ℝ)) : ℝ) ^ 2 =
      (α - β ^ 2) * (m : ℝ) ^ 2 +
        (m : ℝ) *
          (bkrCeilError α m - 2 * β * bkrCeilError β m) -
        (bkrCeilError β m) ^ 2 := by
  unfold bkrCeilError
  ring

noncomputable def bkr_goodWindow_exponent_real
    (α β ε : ℝ) (m : ℕ) (hm : 0 < m)
    (hgood : bkrGoodRoundingWindow α β ε m) :
    (α - β ^ 2) * (m : ℝ) ^ 2 ≤
      (m : ℝ) * (Nat.ceil (α * (m : ℝ)) : ℝ) -
        (Nat.ceil (β * (m : ℝ)) : ℝ) ^ 2 := by
  rw [bkr_rounding_exponent_identity]
  unfold bkrGoodRoundingWindow at hgood
  dsimp only at hgood
  rcases hgood with hzero | hineq
  · rcases hzero with ⟨ha, hb⟩
    rw [ha, hb]
    norm_num
  · rcases hineq with ⟨_hfract, hineq⟩
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hdiv :
        (bkrCeilError β m) ^ 2 / (m : ℝ) ≤
          bkrCeilError α m - 2 * β * bkrCeilError β m := by
      linarith
    have hmul := (div_le_iff₀ hmR).mp hdiv
    nlinarith

noncomputable def bkr_goodWindow_size
    (α β ε : ℝ) (m : ℕ) (hhard : β ^ 2 < α)
    (hm : 0 < m) (hgood : bkrGoodRoundingWindow α β ε m) :
    (Nat.ceil (β * (m : ℝ))) ^ 2 ≤
      Nat.ceil (α * (m : ℝ)) * m := by
  have hreal := bkr_goodWindow_exponent_real α β ε m hm hgood
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hbase : 0 < (α - β ^ 2) * (m : ℝ) ^ 2 := by
    positivity
  have hcast :
      (Nat.ceil (β * (m : ℝ)) : ℝ) ^ 2 ≤
        (Nat.ceil (α * (m : ℝ)) : ℝ) * (m : ℝ) := by
    nlinarith
  exact_mod_cast hcast

noncomputable def bkr_target_exponent_of_goodWindow
    (α β ε : ℝ) (m : ℕ) (hhard : β ^ 2 < α)
    (hm : 0 < m) (hgood : bkrGoodRoundingWindow α β ε m) :
    (((2 ^ m : ℕ) : ℝ) ^
        ((α - β ^ 2) * Real.logb 2 (2 ^ m : ℕ))) ≤
      (2 : ℝ) ^
        ((((Nat.ceil (α * (m : ℝ))) * m -
          (Nat.ceil (β * (m : ℝ))) ^ 2 : ℕ) : ℝ)) := by
  have hsize := bkr_goodWindow_size α β ε m hhard hm hgood
  have hreal := bkr_goodWindow_exponent_real α β ε m hm hgood
  have hlog :
      Real.logb 2 (((2 ^ m : ℕ) : ℝ)) = (m : ℝ) := by
    norm_num only [Nat.cast_ofNat, Nat.cast_pow]
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  have hleft :
      (((2 ^ m : ℕ) : ℝ) ^
          ((α - β ^ 2) * Real.logb 2 (2 ^ m : ℕ))) =
        (2 : ℝ) ^ ((α - β ^ 2) * (m : ℝ) ^ 2) := by
    rw [hlog]
    norm_num only [Nat.cast_ofNat, Nat.cast_pow]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsub :
      ((((Nat.ceil (α * (m : ℝ))) * m -
          (Nat.ceil (β * (m : ℝ))) ^ 2 : ℕ) : ℝ)) =
        (Nat.ceil (α * (m : ℝ)) : ℝ) * (m : ℝ) -
          (Nat.ceil (β * (m : ℝ)) : ℝ) ^ 2 := by
    rw [Nat.cast_sub hsize]
    norm_num only [Nat.cast_mul, Nat.cast_pow]
  rw [hleft, hsub]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith

noncomputable def bkr_two_pow_rpow
    (α : ℝ) (m : ℕ) :
    (((2 ^ m : ℕ) : ℝ) ^ α) =
      (2 : ℝ) ^ (α * (m : ℝ)) := by
  norm_num only [Nat.cast_ofNat, Nat.cast_pow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

noncomputable def bkr_eventual_degree_bound_of_goodWindow
    (α β ε : ℝ) (hα : 0 < α) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      bkrGoodRoundingWindow α β ε m →
      2 ^ (Nat.ceil (α * (m : ℝ)) - 1) <
        Nat.floor ((((2 ^ m : ℕ) : ℝ) ^ α)) := by
  obtain ⟨ms, hslack⟩ := bkr_degree_slack_eventually α ε hα hε
  refine ⟨max 1 ms, fun m hm hgood => ?_⟩
  have hmpos : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_max_left 1 ms).trans hm)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hα0 : 0 ≤ α := hα.le
  have hslackm := hslack m ((Nat.le_max_right 1 ms).trans hm)
  unfold bkrGoodRoundingWindow at hgood
  dsimp only at hgood
  rcases hgood with hzero | hwindow
  · rcases hzero with ⟨ha, _hb⟩
    have hy :
        α * (m : ℝ) = (Nat.ceil (α * (m : ℝ)) : ℝ) := by
      unfold bkrCeilError at ha
      linarith
    rw [bkr_two_pow_rpow, hy]
    simp only [Nat.ceil_natCast, Real.rpow_natCast]
    have hfloor :
        Nat.floor ((2 : ℝ) ^ Nat.ceil (α * (m : ℝ))) =
          2 ^ Nat.ceil (α * (m : ℝ)) := by
      have hpcast :
          (2 : ℝ) ^ Nat.ceil (α * (m : ℝ)) =
            ((2 ^ Nat.ceil (α * (m : ℝ)) : ℕ) : ℝ) := by
        norm_num only [Nat.cast_ofNat, Nat.cast_pow]
      rw [hpcast, Nat.floor_natCast]
    rw [hfloor]
    exact (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2))
      (by
        have hUpos : 0 < Nat.ceil (α * (m : ℝ)) :=
          Nat.ceil_pos.mpr (mul_pos hα hmR)
        omega)
  · rcases hwindow with ⟨hfractLower, _hround⟩
    have hfract0 : Int.fract (α * (m : ℝ)) ≠ 0 := by
      intro hz
      rw [hz] at hfractLower
      linarith
    have hu :
        Nat.ceil (α * (m : ℝ)) - 1 =
          Nat.floor (α * (m : ℝ)) :=
      bkr_ceil_sub_one_eq_floor α m hα0 hfract0
    rw [hu]
    apply (Nat.lt_iff_add_one_le).mpr
    rw [Nat.le_floor_iff (by positivity)]
    rw [bkr_two_pow_rpow]
    have hpowfract :
        (2 : ℝ) ^ ε ≤
          (2 : ℝ) ^ Int.fract (α * (m : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfractLower
    have hprod :
        (2 : ℝ) ^ Nat.floor (α * (m : ℝ)) * (2 : ℝ) ^ ε ≤
          (2 : ℝ) ^ Nat.floor (α * (m : ℝ)) *
            (2 : ℝ) ^ Int.fract (α * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hpowfract (by positivity)
    have hstrict :
        (2 : ℝ) ^ Nat.floor (α * (m : ℝ)) + 1 <
          (2 : ℝ) ^ Nat.floor (α * (m : ℝ)) * (2 : ℝ) ^ ε := by
      nlinarith
    have hdecomp :
        (2 : ℝ) ^ Nat.floor (α * (m : ℝ)) *
            (2 : ℝ) ^ Int.fract (α * (m : ℝ)) =
          (2 : ℝ) ^ (α * (m : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      calc
        (Nat.floor (α * (m : ℝ)) : ℝ) +
            Int.fract (α * (m : ℝ)) =
          (Int.floor (α * (m : ℝ)) : ℝ) +
            Int.fract (α * (m : ℝ)) := by
              rw [natCast_floor_eq_intCast_floor
                (mul_nonneg hα0 (Nat.cast_nonneg m))]
        _ = α * (m : ℝ) := Int.floor_add_fract _
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
    exact (hstrict.trans_le hprod).le.trans_eq hdecomp

noncomputable def bkr_eventual_arithmetic_bridge
    (α β ε : ℝ) (hα_pos : 0 < α) (hα_lt : α < β)
    (hβ_lt : β < 1) (hhard : β ^ 2 < α) (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      bkrGoodRoundingWindow α β ε m →
      bkrLooseParameters α β m
        (Nat.ceil (α * (m : ℝ)) - 1)
        (Nat.ceil (β * (m : ℝ))) := by
  obtain ⟨md, hdegree⟩ :=
    bkr_eventual_degree_bound_of_goodWindow α β ε hα_pos hε
  refine ⟨max 1 md, fun m hm hgood => ?_⟩
  have hmpos : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one ((Nat.le_max_left 1 md).trans hm)
  obtain ⟨huv, hvm⟩ :=
    bkr_ceil_parameters_order α β m hα_pos hα_lt hβ_lt hmpos
  have hUpos : 0 < Nat.ceil (α * (m : ℝ)) := by
    apply Nat.ceil_pos.mpr
    exact mul_pos hα_pos (by exact_mod_cast hmpos)
  have hpred :
      (Nat.ceil (α * (m : ℝ)) - 1) + 1 =
        Nat.ceil (α * (m : ℝ)) := by
    omega
  have hsize := bkr_goodWindow_size α β ε m hhard hmpos hgood
  have hdeg := hdegree m ((Nat.le_max_right 1 md).trans hm) hgood
  have hradius := bkr_radius_of_ceil β m
  have hexponent :=
    bkr_target_exponent_of_goodWindow α β ε m hhard hmpos hgood
  unfold bkrLooseParameters
  refine ⟨hmpos, huv, hvm, ?_, hdeg, hradius, ?_⟩
  · rw [hpred]
    exact hsize
  · rw [hpred]
    exact hexponent

open Filter Function Set in
open scoped Topology in
noncomputable def bkr_unbounded_good_windows_alpha_irrational_beta_rational
    (α β : ℝ) (hα_pos : 0 < α) (hβ0 : 0 ≤ β)
    (hαirr : Irrational α) (hβrat : ¬ Irrational β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ m : ℕ,
      N < m ∧ bkrGoodRoundingWindow α β ε m := by
  obtain ⟨D, hD, z, hβD⟩ :=
    bkr_rational_has_denominator_multiple β hβrat
  have hDirr : Irrational (α * (D : ℝ)) :=
    hαirr.mul_natCast (Nat.ne_of_gt hD)
  refine ⟨(1 : ℝ) / 4, by norm_num, fun N => ?_⟩
  obtain ⟨n, hn, hfrac⟩ :=
    bkr_irrational_rotation_hits_fract_interval
      (α * (D : ℝ)) ((1 : ℝ) / 4) ((1 : ℝ) / 2)
      hDirr (by norm_num) (by norm_num) (by norm_num) N
  let m : ℕ := D * n
  have hnm : n ≤ m := by
    dsimp only [m]
    calc
      n = 1 * n := by omega
      _ ≤ D * n := Nat.mul_le_mul_right n hD
  have hmN : N < m := hn.trans_le hnm
  have hαm :
      α * (m : ℝ) = (α * (D : ℝ)) * (n : ℝ) := by
    dsimp only [m]
    push_cast
    ring
  have hfa :
      Int.fract (α * (m : ℝ)) ∈
        Set.Ioo ((1 : ℝ) / 4) ((1 : ℝ) / 2) := by
    rw [hαm]
    exact hfrac
  have hfa0 : Int.fract (α * (m : ℝ)) ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num) hfa.1)
  have hfb0 : Int.fract (β * (m : ℝ)) = 0 := by
    dsimp only [m]
    push_cast
    rw [show β * ((D : ℝ) * (n : ℝ)) =
      (β * (D : ℝ)) * (n : ℝ) by ring]
    rw [hβD]
    rw [← Int.cast_natCast n]
    rw [← Int.cast_mul]
    exact Int.fract_intCast (z * (n : ℤ))
  refine ⟨m, hmN, ?_⟩
  exact bkrGoodRoundingWindow_of_beta_fract_zero
    α β ((1 : ℝ) / 4) m hα_pos.le hβ0 hfa0 hfb0 hfa.1.le

noncomputable def bkr_unbounded_good_windows_both_rational
    (α β : ℝ) (hα_pos : 0 < α) (hβ_pos : 0 < β)
    (hαrat : ¬ Irrational α) (hβrat : ¬ Irrational β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ m : ℕ,
      N < m ∧ bkrGoodRoundingWindow α β ε m := by
  obtain ⟨Dα, hDα, zα, hαD⟩ :=
    bkr_rational_has_denominator_multiple α hαrat
  obtain ⟨Dβ, hDβ, zβ, hβD⟩ :=
    bkr_rational_has_denominator_multiple β hβrat
  refine ⟨1, by norm_num, fun N => ?_⟩
  let m : ℕ := Dα * Dβ * (N + 1)
  have hm : N < m := by
    dsimp [m]
    have hprod : 1 ≤ Dα * Dβ := Nat.one_le_iff_ne_zero.mpr (by
      exact Nat.mul_ne_zero (Nat.ne_of_gt hDα) (Nat.ne_of_gt hDβ))
    nlinarith
  have hαm :
      α * (m : ℝ) =
        ((zα * (Dβ * (N + 1) : ℕ) : ℤ) : ℝ) := by
    dsimp [m]
    push_cast
    rw [show α * (Dα * Dβ * (N + 1) : ℝ) =
      (α * Dα) * (Dβ * (N + 1)) by ring]
    rw [hαD]
  have hβm :
      β * (m : ℝ) =
        ((zβ * (Dα * (N + 1) : ℕ) : ℤ) : ℝ) := by
    dsimp [m]
    push_cast
    rw [show β * (Dα * Dβ * (N + 1) : ℝ) =
      (β * Dβ) * (Dα * (N + 1)) by ring]
    rw [hβD]
  have ha : bkrCeilError α m = 0 :=
    bkrCeilError_eq_zero_of_eq_intCast α m hα_pos.le _ hαm
  have hb : bkrCeilError β m = 0 :=
    bkrCeilError_eq_zero_of_eq_intCast β m hβ_pos.le _ hβm
  refine ⟨m, hm, ?_⟩
  unfold bkrGoodRoundingWindow
  dsimp only
  exact Or.inl ⟨ha, hb⟩

open Filter Function Set in
open scoped Topology in
def bkr_zsmul_closure_arbitrarily_late_hit
    {G : Type} [AddGroup G] [TopologicalSpace G] [CompactSpace G]
    [IsTopologicalAddGroup G] (x z : G)
    (hz : z ∈ closure (Set.range fun n : ℤ => n • x))
    {U : Set G} (hUopen : IsOpen U) (hzU : z ∈ U) :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ m • x ∈ U := by
  have hcluster :
      MapClusterPt z Filter.atTop (fun n : ℕ => n • x) :=
    ((bkr_mapClusterPt_atTop_nsmul_tfae z x).out 3 0).mp hz
  have hfreq : ∃ᶠ n : ℕ in Filter.atTop, n • x ∈ U :=
    hcluster.frequently (hUopen.mem_nhds hzU)
  exact Filter.frequently_atTop'.mp hfreq

open Filter Function Set in
open scoped Topology Pointwise in
noncomputable def
    bkr_unbounded_good_windows_of_horizontalKernel_ne_bot
    (α β : ℝ) (hα0 : 0 ≤ α) (hβpos : 0 < β)
    (hβlt : β < 1) (hβirr : Irrational β)
    (hK : bkrHorizontalKernel α β ≠ ⊥) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ m : ℕ,
      N < m ∧ bkrGoodRoundingWindow α β ε m := by
  obtain ⟨d, hd0, hdhalf, z, hzcl, hzfst, hzsnd⟩ :=
    bkr_exists_middle_rectangle_point_of_horizontalKernel_ne_bot
      α β hβirr hK
  let U : Set (UnitAddCircle × UnitAddCircle) :=
    bkrAddCircleInterval (d / 4) (1 - d / 4) ×ˢ
      bkrAddCircleInterval (1 - d / 16) (1 - d / 64)
  have hfstOpen :
      IsOpen (bkrAddCircleInterval (d / 4) (1 - d / 4)) := by
    apply bkrAddCircleInterval_isOpen
    · linarith
    · nlinarith
    · linarith
  have hsndOpen :
      IsOpen (bkrAddCircleInterval
        (1 - d / 16) (1 - d / 64)) := by
    apply bkrAddCircleInterval_isOpen
    · nlinarith
    · nlinarith
    · linarith
  have hUopen : IsOpen U := hfstOpen.prod hsndOpen
  have hzU : z ∈ U := Set.mem_prod.mpr ⟨hzfst, hzsnd⟩
  refine ⟨d / 4, by linarith, fun N => ?_⟩
  obtain ⟨m, hmN, hmU⟩ :=
    bkr_zsmul_closure_arbitrarily_late_hit
      ((α : UnitAddCircle), (β : UnitAddCircle)) z hzcl
      hUopen hzU N
  have hmcoords := Set.mem_prod.mp hmU
  have hmfst := hmcoords.1
  have hmsnd := hmcoords.2
  change m • (α : UnitAddCircle) ∈
    bkrAddCircleInterval (d / 4) (1 - d / 4) at hmfst
  change m • (β : UnitAddCircle) ∈
    bkrAddCircleInterval (1 - d / 16) (1 - d / 64) at hmsnd
  have hfa :=
    (bkrAddCircleInterval_nsmul_mem_iff
      α (d / 4) (1 - d / 4) m).mp hmfst
  have hfb :=
    (bkrAddCircleInterval_nsmul_mem_iff
      β (1 - d / 16) (1 - d / 64) m).mp hmsnd
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le N) hmN
  have hmone : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hmpos.ne')
  have heta0 : 0 ≤ d / 16 := by linarith
  have heta1 : d / 16 ≤ 1 := by linarith
  have hsq : (d / 16) ^ 2 ≤ d / 16 := by
    nlinarith [sq_nonneg (d / 16)]
  have hdiv : (d / 16) ^ 2 / (m : ℝ) ≤ (d / 16) ^ 2 :=
    div_le_self (sq_nonneg (d / 16)) hmone
  have hlin0 : β * (d / 16) ≤ d / 16 := by
    have := mul_le_mul_of_nonneg_right hβlt.le heta0
    simpa only [one_mul] using this
  have hineq :
      2 * β * (d / 16) + (d / 16) ^ 2 / (m : ℝ) ≤
        1 - (1 - d / 4) := by
    nlinarith
  have hfa0 : Int.fract (α * (m : ℝ)) ≠ 0 := by
    exact ne_of_gt (lt_trans (by linarith : 0 < d / 4) hfa.1)
  have hfb0 : Int.fract (β * (m : ℝ)) ≠ 0 := by
    exact ne_of_gt (lt_trans (by nlinarith : 0 < 1 - d / 16) hfb.1)
  refine ⟨m, hmN, ?_⟩
  exact bkrGoodRoundingWindow_of_fract_bounds
    α β (d / 4) (d / 16) (1 - d / 4) m
    hα0 hβpos.le hmpos heta0 hfa0 hfb0
    hfa.1.le hfa.2.le hfb.1.le hineq

noncomputable def finiteField_charTwo_charP
    {F : Type} [Field F] [Fintype F]
    (m : ℕ) (hcard : Fintype.card F = 2 ^ m) : CharP F 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow hcard

noncomputable def finiteField_charTwo_algebra
    {F : Type} [Field F] [Fintype F]
    (m : ℕ) (hcard : Fintype.card F = 2 ^ m) :
    Algebra (ZMod 2) F := by
  letI : CharP F 2 := finiteField_charTwo_charP m hcard
  exact ZMod.algebra F 2

noncomputable def finiteField_charTwo_finrank
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F]
    (m : ℕ) (hcard : Fintype.card F = 2 ^ m) :
    Module.finrank (ZMod 2) F = m := by
  have hp : 2 ^ Module.finrank (ZMod 2) F = 2 ^ m :=
    (FiniteField.pow_finrank_eq_card 2 F).trans hcard
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hp

def hammingDist_le_card_sub_card_of_agree_on
    {ι F : Type} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (c w : ι → F) (S : Finset ι)
    (hagree : ∀ i ∈ S, c i = w i) :
    hammingDist c w ≤ Fintype.card ι - S.card := by
  rw [hammingDist]
  calc
    (Finset.univ.filter (fun i => c i ≠ w i)).card ≤ Sᶜ.card := by
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_compl]
      intro his
      exact (Finset.mem_filter.mp hi).2 (hagree i his)
    _ = Fintype.card ι - S.card := Finset.card_compl S

noncomputable def rsFrobeniusMapSpace_finrank
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    Module.finrank F (L →ₗ[ZMod 2] F) = v := by
  letI : Module.Finite (ZMod 2) L := Module.Finite.of_finite
  rw [Module.finrank_linearMap_self]
  exact hfin

noncomputable def rsFrobeniusPowerMap
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (j : ℕ) : L →ₗ[ZMod 2] F :=
  ((FiniteField.frobeniusAlgHom (ZMod 2) F) ^ j).toLinearMap.comp L.subtype

noncomputable def rsFrobeniusFamily
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ) :
    Fin (v + 1) → (L →ₗ[ZMod 2] F) :=
  fun j => rsFrobeniusPowerMap L j.1

noncomputable def rsFrobeniusFamily_not_linearIndependent
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    ¬ LinearIndependent F (rsFrobeniusFamily L v) := by
  letI : Module.Finite (ZMod 2) L := Module.Finite.of_finite
  intro hLI
  have hcard := hLI.fintype_card_le_finrank
  rw [rsFrobeniusMapSpace_finrank L v hfin] at hcard
  simp only [Fintype.card_fin] at hcard
  omega

open scoped BigOperators in
noncomputable def rsFrobeniusFamily_relation
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    ∃ a : Fin (v + 1) → F,
      (∑ j : Fin (v + 1), a j • rsFrobeniusFamily L v j) = 0 ∧
      ∃ j : Fin (v + 1), a j ≠ 0 := by
  exact Fintype.not_linearIndependent_iff.mp
    (rsFrobeniusFamily_not_linearIndependent L v hfin)

noncomputable def rsFrobeniusPowerMap_apply
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (j : ℕ) (x : L) :
    rsFrobeniusPowerMap L j x = (x : F) ^ (2 ^ j) := by
  change ((FiniteField.frobeniusAlgHom (ZMod 2) F) ^ j) (x : F) =
    (x : F) ^ (2 ^ j)
  rw [AlgHom.coe_pow]
  induction j with
  | zero =>
      simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      rw [FiniteField.frobeniusAlgHom_apply, ZMod.card]
      rw [← pow_mul]
      rw [pow_succ]

open scoped BigOperators in
noncomputable def rsLinearizedPolynomial
    {F : Type} [Semiring F] (v : ℕ) (a : Fin (v + 1) → F) : Polynomial F :=
  ∑ j : Fin (v + 1), Polynomial.monomial (2 ^ (j : ℕ)) (a j)

open scoped BigOperators in
noncomputable def rsLinearizedPolynomial_coeff_eq_zero
    {F : Type} [Semiring F] (v : ℕ) (a : Fin (v + 1) → F) (n : ℕ)
    (hn : ∀ j : Fin (v + 1), n ≠ 2 ^ (j : ℕ)) :
    (rsLinearizedPolynomial v a).coeff n = 0 := by
  classical
  unfold rsLinearizedPolynomial
  rw [Polynomial.finset_sum_coeff Finset.univ]
  apply Finset.sum_eq_zero
  intro j _hj
  rw [Polynomial.coeff_monomial, if_neg]
  exact fun h => hn j h.symm

open scoped BigOperators in
noncomputable def rsLinearizedPolynomial_coeff_pow
    {F : Type} [Semiring F] (v : ℕ) (a : Fin (v + 1) → F)
    (j : Fin (v + 1)) :
    (rsLinearizedPolynomial v a).coeff (2 ^ (j : ℕ)) = a j := by
  classical
  unfold rsLinearizedPolynomial
  rw [Polynomial.finset_sum_coeff Finset.univ]
  rw [Fintype.sum_eq_single j]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro i hij
    rw [Polynomial.coeff_monomial, if_neg]
    intro hpow
    apply hij
    apply Fin.ext
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow

open scoped BigOperators in
noncomputable def rsLinearizedPolynomial_eval
    {F : Type} [Semiring F] (v : ℕ) (a : Fin (v + 1) → F) (x : F) :
    (rsLinearizedPolynomial v a).eval x =
      ∑ j : Fin (v + 1), a j * x ^ (2 ^ (j : ℕ)) := by
  classical
  unfold rsLinearizedPolynomial
  rw [Polynomial.eval_finset_sum Finset.univ]
  simp only [Finset.mem_univ, Polynomial.eval_monomial]

open scoped BigOperators in
noncomputable def rsFrobeniusRelationPolynomial
    {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    ∃ a : Fin (v + 1) → F,
      rsLinearizedPolynomial v a ≠ 0 ∧
      ∀ x : L, (rsLinearizedPolynomial v a).eval (x : F) = 0 := by
  obtain ⟨a, hrel, j, hj⟩ := rsFrobeniusFamily_relation L v hfin
  refine ⟨a, ?_, ?_⟩
  · intro hp
    have hc : (rsLinearizedPolynomial v a).coeff (2 ^ (j : ℕ)) = 0 := by
      rw [hp, Polynomial.coeff_zero]
    rw [rsLinearizedPolynomial_coeff_pow] at hc
    exact hj hc
  · intro x
    rw [rsLinearizedPolynomial_eval]
    have hx := congrArg (LinearMap.applyₗ' F x) hrel
    simpa only [map_sum, map_smul, map_zero,
      LinearMap.applyₗ'_apply_apply, rsFrobeniusFamily,
      rsFrobeniusPowerMap_apply, smul_eq_mul] using hx

open scoped BigOperators in
noncomputable def rsLinearizedPolynomial_natDegree_le
    {F : Type} [Semiring F] (v : ℕ) (a : Fin (v + 1) → F) :
    (rsLinearizedPolynomial v a).natDegree ≤ 2 ^ v := by
  classical
  unfold rsLinearizedPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le Finset.univ
  intro j _hj
  exact (Polynomial.natDegree_monomial_le (a j)).trans
    (pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2)
      (Nat.le_of_lt_succ j.isLt))

noncomputable def rsFrobeniusRelationPolynomial_saturated
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    ∃ a : Fin (v + 1) → F,
      rsLinearizedPolynomial v a ≠ 0 ∧
      (rsLinearizedPolynomial v a).natDegree = 2 ^ v ∧
      ∀ x : L, (rsLinearizedPolynomial v a).eval (x : F) = 0 := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  obtain ⟨a, hp, hvan⟩ := rsFrobeniusRelationPolynomial L v hfin
  let e : L ↪ F := ⟨fun x => (x : F), Subtype.coe_injective⟩
  let S : Finset F := Finset.univ.map e
  have hcardL : Fintype.card L = 2 ^ v := by
    calc
      Fintype.card L = Fintype.card (ZMod 2) ^
          Module.finrank (ZMod 2) L := Module.card_eq_pow_finrank
      _ = 2 ^ v := by rw [ZMod.card, hfin]
  have hcardS : S.card = 2 ^ v := by
    simpa only [S, Finset.card_map, Finset.card_univ] using hcardL
  have hS : ∀ x ∈ S, (rsLinearizedPolynomial v a).eval x = 0 := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact hvan y
  have hdeg_le : (rsLinearizedPolynomial v a).natDegree ≤ S.card := by
    rw [hcardS]
    exact rsLinearizedPolynomial_natDegree_le v a
  have hroots := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    hS hdeg_le hp
  have hdeg_ge : 2 ^ v ≤ (rsLinearizedPolynomial v a).natDegree := by
    have hcr := Polynomial.card_roots' (rsLinearizedPolynomial v a)
    rw [hroots] at hcr
    rw [← hcardS, Finset.card_def]
    exact hcr
  exact ⟨a, hp,
    le_antisymm (rsLinearizedPolynomial_natDegree_le v a) hdeg_ge, hvan⟩

open scoped BigOperators in
noncomputable def rsLinearizedPolynomial_scale
    {F : Type} [Semiring F] (v : ℕ) (a : Fin (v + 1) → F) (c : F) :
    rsLinearizedPolynomial v (fun j => c * a j) =
      Polynomial.C c * rsLinearizedPolynomial v a := by
  classical
  unfold rsLinearizedPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Polynomial.C_mul_monomial]

noncomputable def rsLinearizedPolynomial_normalized
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    ∃ a : Fin (v + 1) → F,
      a ⟨v, by omega⟩ = 1 ∧
      (rsLinearizedPolynomial v a).Monic ∧
      ∀ x : L, (rsLinearizedPolynomial v a).eval (x : F) = 0 := by
  obtain ⟨a₀, hp, hdeg, hvan⟩ :=
    rsFrobeniusRelationPolynomial_saturated L v hfin
  let top : Fin (v + 1) := ⟨v, by omega⟩
  let c : F := a₀ top
  have hcoeff : (rsLinearizedPolynomial v a₀).coeff (2 ^ v) = c := by
    exact rsLinearizedPolynomial_coeff_pow v a₀ top
  have hc : c ≠ 0 := by
    intro hc0
    have hcoeff0 : (rsLinearizedPolynomial v a₀).coeff (2 ^ v) = 0 :=
      hcoeff.trans hc0
    have hlc0 : (rsLinearizedPolynomial v a₀).leadingCoeff = 0 := by
      rw [← Polynomial.coeff_natDegree, hdeg]
      exact hcoeff0
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp) hlc0
  let a : Fin (v + 1) → F := fun j => c⁻¹ * a₀ j
  have hatop : a top = 1 := by
    dsimp only [a, c]
    exact inv_mul_cancel₀ hc
  refine ⟨a, ?_, ?_, ?_⟩
  · exact hatop
  · apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (2 ^ v)
    · exact rsLinearizedPolynomial_natDegree_le v a
    · exact (rsLinearizedPolynomial_coeff_pow v a top).trans hatop
  · intro x
    rw [rsLinearizedPolynomial_scale]
    rw [Polynomial.eval_mul, Polynomial.eval_C, hvan x, mul_zero]

open scoped BigOperators in
noncomputable def rsSubspacePolynomial
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (L : Submodule (ZMod 2) F) : Polynomial F := by
  letI : Fintype L := Fintype.ofFinite L
  exact ∏ x : L, (Polynomial.X - Polynomial.C (x : F))

noncomputable def bkrFiberCenter
    {ι F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (domain : ι ↪ F) (pivot : Submodule (ZMod 2) F) : ι → F :=
  ReedSolomon.evalOnPoints domain (rsSubspacePolynomial pivot)

noncomputable def bkrFiberCodeword
    {ι F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (domain : ι ↪ F) (pivot L : Submodule (ZMod 2) F) : ι → F :=
  ReedSolomon.evalOnPoints domain
    (rsSubspacePolynomial pivot - rsSubspacePolynomial L)

noncomputable def rsCoefficientProfile
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (a b : ℕ)
    (L : Submodule (ZMod 2) F) :
    {j : ℕ // j ∈ Finset.Ico a b} → F :=
  fun j => (rsSubspacePolynomial L).coeff (2 ^ j.1)

def bkrCoefficientFiber
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (a b v : ℕ)
    (profile : {j : ℕ // j ∈ Finset.Ico a b} → F) :
    Set (Submodule (ZMod 2) F) :=
  {L | L ∈ bkrSubspaceFamily v ∧ rsCoefficientProfile a b L = profile}

noncomputable def bkrGraphCoefficientProfile
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (m u v : ℕ) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m)
    (f : (Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) :
    {j : ℕ // j ∈ Finset.Ico (u + 1) v} → F :=
  rsCoefficientProfile (u + 1) v
    (bkrTransportedGraph m v hvm hfin f)

noncomputable def bkrGraphProfileFiber
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (m u v : ℕ) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m)
    (profile : {j : ℕ // j ∈ Finset.Ico (u + 1) v} → F) :
    Finset ((Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) := by
  classical
  letI : Module.Finite (ZMod 2)
      ((Fin v → ZMod 2) →ₗ[ZMod 2]
        (Fin (m - v) → ZMod 2)) :=
    Module.Finite.linearMap (ZMod 2) (ZMod 2)
      (Fin v → ZMod 2) (Fin (m - v) → ZMod 2)
  letI : Finite ((Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) :=
    Module.finite_of_finite (ZMod 2)
  letI : Fintype ((Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) := Fintype.ofFinite _
  exact Finset.univ.filter
    (fun f => bkrGraphCoefficientProfile m u v hvm hfin f = profile)

noncomputable def bkr_exists_large_graph_profile
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (m u v : ℕ) (huv : u < v) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m)
    (hcard : Fintype.card F = 2 ^ m)
    (hsize : v ^ 2 ≤ (u + 1) * m) :
    ∃ profile : {j : ℕ // j ∈ Finset.Ico (u + 1) v} → F,
      2 ^ ((u + 1) * m - v ^ 2) ≤
        (bkrGraphProfileFiber m u v hvm hfin profile).card := by
  classical
  letI : Module.Finite (ZMod 2)
      ((Fin v → ZMod 2) →ₗ[ZMod 2]
        (Fin (m - v) → ZMod 2)) :=
    Module.Finite.linearMap (ZMod 2) (ZMod 2)
      (Fin v → ZMod 2) (Fin (m - v) → ZMod 2)
  letI : Finite ((Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) :=
    Module.finite_of_finite (ZMod 2)
  letI : Fintype ((Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) := Fintype.ofFinite _
  letI : Fintype {j : ℕ // j ∈ Finset.Ico (u + 1) v} :=
    Fintype.ofFinite _
  have hdomain : Fintype.card ((Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2)) = 2 ^ (v * (m - v)) := by
    simpa only [Nat.card_eq_fintype_card] using bkrGraphParameter_card m v
  have hprofiles :
      Fintype.card ({j : ℕ // j ∈ Finset.Ico (u + 1) v} → F) =
        (2 ^ m) ^ (v - u - 1) := by
    simpa only [Nat.card_eq_fintype_card] using
      bkrCoefficientProfile_card m u v hcard
  have hmul :
      Fintype.card ({j : ℕ // j ∈ Finset.Ico (u + 1) v} → F) *
          2 ^ ((u + 1) * m - v ^ 2) ≤
        Fintype.card ((Fin v → ZMod 2) →ₗ[ZMod 2]
          (Fin (m - v) → ZMod 2)) := by
    rw [hprofiles, hdomain]
    apply le_of_eq
    calc
      (2 ^ m) ^ (v - u - 1) * 2 ^ ((u + 1) * m - v ^ 2) =
          2 ^ (m * (v - u - 1)) *
            2 ^ ((u + 1) * m - v ^ 2) := by
        rw [pow_mul]
      _ = 2 ^ (m * (v - u - 1) + ((u + 1) * m - v ^ 2)) := by
        rw [pow_add]
      _ = 2 ^ (v * (m - v)) := by
        rw [bkr_profile_exponent_identity m u v huv hvm hsize]
  obtain ⟨profile, hprofile⟩ :=
    Fintype.exists_le_card_fiber_of_mul_le_card
      (bkrGraphCoefficientProfile m u v hvm hfin) hmul
  refine ⟨profile, ?_⟩
  have hfiber_eq :
      Finset.univ.filter (fun f =>
        bkrGraphCoefficientProfile m u v hvm hfin f = profile) =
        bkrGraphProfileFiber m u v hvm hfin profile := by
    ext f
    simp only [bkrGraphProfileFiber, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [← hfiber_eq]
  exact hprofile

noncomputable def rsDifferencePolynomial
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (pivot L : Submodule (ZMod 2) F) : Polynomial F :=
  rsSubspacePolynomial pivot - rsSubspacePolynomial L

open scoped BigOperators in
noncomputable def rsSubspacePolynomial_eval_eq_zero_iff
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (L : Submodule (ZMod 2) F) (x : F) :
    (rsSubspacePolynomial L).eval x = 0 ↔ x ∈ L := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  change Polynomial.eval x
      ((Finset.univ : Finset L).prod
        (fun a => Polynomial.X - Polynomial.C (a : F))) = 0 ↔ x ∈ L
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]
  constructor
  · rintro ⟨a, ha⟩
    rw [ha]
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

noncomputable def bkrFiberCodeword_agrees_on_subspace
    {ι F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (domain : ι ↪ F) (pivot L : Submodule (ZMod 2) F)
    (i : ι) (hi : domain i ∈ L) :
    bkrFiberCodeword domain pivot L i = bkrFiberCenter domain pivot i := by
  unfold bkrFiberCodeword bkrFiberCenter ReedSolomon.evalOnPoints
  change (rsSubspacePolynomial pivot - rsSubspacePolynomial L).eval (domain i) =
    (rsSubspacePolynomial pivot).eval (domain i)
  rw [Polynomial.eval_sub, (rsSubspacePolynomial_eval_eq_zero_iff L (domain i)).mpr hi,
    sub_zero]

noncomputable def bkrFiberCodeword_hammingDist_le
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (e : ι ≃ F) (pivot L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    hammingDist (bkrFiberCodeword e.toEmbedding pivot L)
        (bkrFiberCenter e.toEmbedding pivot) ≤
      Fintype.card ι - 2 ^ v := by
  calc
    hammingDist (bkrFiberCodeword e.toEmbedding pivot L)
        (bkrFiberCenter e.toEmbedding pivot) ≤
        Fintype.card ι - (bkrSubspaceCoordinateFinset e L).card := by
      apply hammingDist_le_card_sub_card_of_agree_on
      intro i hi
      exact bkrFiberCodeword_agrees_on_subspace e.toEmbedding pivot L i
        (bkrSubspaceCoordinateFinset_mem e L i hi)
    _ = Fintype.card ι - 2 ^ v := by
      rw [bkrSubspaceCoordinateFinset_card e L v hfin]

noncomputable def rsSubspacePolynomial_injective
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] :
    Function.Injective
      (rsSubspacePolynomial : Submodule (ZMod 2) F → Polynomial F) := by
  intro L M h
  apply Submodule.ext
  intro x
  rw [← rsSubspacePolynomial_eval_eq_zero_iff L x]
  rw [← rsSubspacePolynomial_eval_eq_zero_iff M x]
  rw [h]

open scoped BigOperators in
noncomputable def rsSubspacePolynomial_linearized
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (L : Submodule (ZMod 2) F) (v : ℕ)
    (hfin : Module.finrank (ZMod 2) L = v) :
    ∃ a : Fin (v + 1) → F,
      a ⟨v, by omega⟩ = 1 ∧
      rsSubspacePolynomial L = rsLinearizedPolynomial v a := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  obtain ⟨a, hatop, hmonic, hvan⟩ :=
    rsLinearizedPolynomial_normalized L v hfin
  let top : Fin (v + 1) := ⟨v, by omega⟩
  let e : L ↪ F := ⟨fun x => (x : F), Subtype.coe_injective⟩
  let S : Finset F := Finset.univ.map e
  have hcardL : Fintype.card L = 2 ^ v := by
    calc
      Fintype.card L = Fintype.card (ZMod 2) ^
          Module.finrank (ZMod 2) L := Module.card_eq_pow_finrank
      _ = 2 ^ v := by rw [ZMod.card, hfin]
  have hcardS : S.card = 2 ^ v := by
    simpa only [S, Finset.card_map, Finset.card_univ] using hcardL
  have hS : ∀ x ∈ S, (rsLinearizedPolynomial v a).eval x = 0 := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact hvan y
  have hdeg : (rsLinearizedPolynomial v a).natDegree = 2 ^ v := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (rsLinearizedPolynomial_natDegree_le v a)
    have htopcoeff := rsLinearizedPolynomial_coeff_pow v a top
    rw [hatop] at htopcoeff
    exact htopcoeff.symm ▸ one_ne_zero
  have hroots := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    hS (by rw [hcardS]; exact rsLinearizedPolynomial_natDegree_le v a)
    hmonic.ne_zero
  have hrootcard :
      (rsLinearizedPolynomial v a).roots.card =
        (rsLinearizedPolynomial v a).natDegree := by
    rw [hroots, ← Finset.card_def, hcardS, hdeg]
  have hprod :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      hmonic hrootcard
  rw [hroots] at hprod
  simp only [S, Finset.map_val, Multiset.map_map, Function.comp_apply] at hprod
  rw [Finset.prod_map_val] at hprod
  refine ⟨a, hatop, ?_⟩
  change (∏ x : L, (Polynomial.X - Polynomial.C (x : F))) =
    rsLinearizedPolynomial v a
  exact hprod

noncomputable def bkr_profile_difference_natDegree_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (m u v : ℕ) (huv : u < v) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m)
    (f g : (Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2))
    (hprofile : bkrGraphCoefficientProfile m u v hvm hfin f =
      bkrGraphCoefficientProfile m u v hvm hfin g) :
    (rsSubspacePolynomial (bkrTransportedGraph m v hvm hfin f) -
      rsSubspacePolynomial (bkrTransportedGraph m v hvm hfin g)).natDegree ≤
        2 ^ u := by
  classical
  obtain ⟨a, hatop, hpa⟩ := rsSubspacePolynomial_linearized
    (bkrTransportedGraph m v hvm hfin f) v
    (bkrTransportedGraph_finrank m v hvm hfin f)
  obtain ⟨b, hbtop, hpb⟩ := rsSubspacePolynomial_linearized
    (bkrTransportedGraph m v hvm hfin g) v
    (bkrTransportedGraph_finrank m v hvm hfin g)
  rw [hpa, hpb]
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases hex : ∃ j : Fin (v + 1), n = 2 ^ (j : ℕ)
  · obtain ⟨j, rfl⟩ := hex
    rw [Polynomial.coeff_sub, rsLinearizedPolynomial_coeff_pow,
      rsLinearizedPolynomial_coeff_pow]
    have huj : u < (j : ℕ) := by
      by_contra hnot
      have hju : (j : ℕ) ≤ u := Nat.le_of_not_gt hnot
      have hpow : 2 ^ (j : ℕ) ≤ 2 ^ u :=
        pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2) hju
      omega
    by_cases hjv : (j : ℕ) < v
    · have hjmem : (j : ℕ) ∈ Finset.Ico (u + 1) v := by
        exact Finset.mem_Ico.mpr ⟨by omega, hjv⟩
      have hcoeff := congrFun hprofile ⟨(j : ℕ), hjmem⟩
      unfold bkrGraphCoefficientProfile rsCoefficientProfile at hcoeff
      rw [hpa, hpb, rsLinearizedPolynomial_coeff_pow,
        rsLinearizedPolynomial_coeff_pow] at hcoeff
      exact sub_eq_zero.mpr hcoeff
    · have hjle : (j : ℕ) ≤ v := Nat.le_of_lt_succ j.isLt
      have hvj : v ≤ (j : ℕ) := Nat.le_of_not_gt hjv
      have hjval : (j : ℕ) = v := Nat.le_antisymm hjle hvj
      have hj : j = (⟨v, by omega⟩ : Fin (v + 1)) := Fin.ext hjval
      rw [hj, hatop, hbtop, sub_self]
  · have hnzero : ∀ j : Fin (v + 1), n ≠ 2 ^ (j : ℕ) := by
      intro j hj
      exact hex ⟨j, hj⟩
    rw [Polynomial.coeff_sub,
      rsLinearizedPolynomial_coeff_eq_zero v a n hnzero,
      rsLinearizedPolynomial_coeff_eq_zero v b n hnzero, sub_zero]

noncomputable def bkr_profile_codeword_eq_imp_eq
    {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (e : ι ≃ F) (m u v : ℕ) (huv : u < v) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m)
    (hcardF : Fintype.card F = 2 ^ m)
    (pivot f g : (Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2))
    (hprofile : bkrGraphCoefficientProfile m u v hvm hfin f =
      bkrGraphCoefficientProfile m u v hvm hfin g)
    (hword : bkrFiberCodeword e.toEmbedding
        (bkrTransportedGraph m v hvm hfin pivot)
        (bkrTransportedGraph m v hvm hfin f) =
      bkrFiberCodeword e.toEmbedding
        (bkrTransportedGraph m v hvm hfin pivot)
        (bkrTransportedGraph m v hvm hfin g)) : f = g := by
  let pf := rsSubspacePolynomial (bkrTransportedGraph m v hvm hfin f)
  let pg := rsSubspacePolynomial (bkrTransportedGraph m v hvm hfin g)
  have hdeg : (pf - pg).natDegree ≤ 2 ^ u :=
    bkr_profile_difference_natDegree_le m u v huv hvm hfin f g hprofile
  have hum : u < m := lt_of_lt_of_le huv hvm
  have hpow : 2 ^ u < 2 ^ m :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)) hum
  have hdegcard : (pf - pg).natDegree < Fintype.card F := by
    rw [hcardF]
    exact hdeg.trans_lt hpow
  have hdegCardinal :
      ((pf - pg).natDegree : Cardinal) < Cardinal.mk F := by
    rw [Cardinal.mk_fintype F]
    exact_mod_cast hdegcard
  have hvan : ∀ x : F, (pf - pg).eval x = 0 := by
    intro x
    have hx := congrFun hword (e.symm x)
    unfold bkrFiberCodeword at hx
    change
      (rsSubspacePolynomial (bkrTransportedGraph m v hvm hfin pivot) - pf).eval
          (e (e.symm x)) =
        (rsSubspacePolynomial (bkrTransportedGraph m v hvm hfin pivot) - pg).eval
          (e (e.symm x)) at hx
    rw [e.apply_symm_apply, Polynomial.eval_sub, Polynomial.eval_sub] at hx
    rw [Polynomial.eval_sub]
    exact sub_eq_zero.mpr (sub_right_inj.mp hx)
  have hpoly : pf - pg = 0 := by
    by_contra hne
    obtain ⟨x, hx⟩ :=
      Polynomial.exists_eval_ne_zero_of_natDegree_lt_card
        (pf - pg) hne hdegCardinal
    exact hx (hvan x)
  apply bkrTransportedGraph_injective m v hvm hfin
  apply rsSubspacePolynomial_injective
  exact sub_eq_zero.mp hpoly

noncomputable def bkr_profile_fiber_codeword_mem_close
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F]
    (e : ι ≃ F) (m u v k : ℕ) (huv : u < v) (hvm : v ≤ m)
    (hfin : Module.finrank (ZMod 2) F = m)
    (hcardι : Fintype.card ι = 2 ^ m) (hdeg : 2 ^ u < k)
    (pivot f : (Fin v → ZMod 2) →ₗ[ZMod 2]
      (Fin (m - v) → ZMod 2))
    (hprofile : bkrGraphCoefficientProfile m u v hvm hfin pivot =
      bkrGraphCoefficientProfile m u v hvm hfin f) :
    bkrFiberCodeword e.toEmbedding
        (bkrTransportedGraph m v hvm hfin pivot)
        (bkrTransportedGraph m v hvm hfin f) ∈
      _root_.ListDecodable.closeCodewordsRel
        ((ReedSolomon.code e.toEmbedding k : Set (ι → F)))
        (bkrFiberCenter e.toEmbedding
          (bkrTransportedGraph m v hvm hfin pivot))
        (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m) := by
  have hcode :
      bkrFiberCodeword e.toEmbedding
          (bkrTransportedGraph m v hvm hfin pivot)
          (bkrTransportedGraph m v hvm hfin f) ∈
        ReedSolomon.code e.toEmbedding k := by
    unfold bkrFiberCodeword
    apply ReedSolomon.evalOnPoints_mem_code_of_natDegree_lt
    exact lt_of_le_of_lt
      (bkr_profile_difference_natDegree_le m u v huv hvm hfin pivot f hprofile) hdeg
  have hdist := bkrFiberCodeword_hammingDist_le e
    (bkrTransportedGraph m v hvm hfin pivot)
    (bkrTransportedGraph m v hvm hfin f) v
    (bkrTransportedGraph_finrank m v hvm hfin f)
  have hfloor :
      Nat.floor ((1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m) * Fintype.card ι) =
        2 ^ m - 2 ^ v := by
    rw [hcardι]
    norm_num only [Nat.cast_ofNat, Nat.cast_pow]
    exact bkr_radius_floor_eq v m hvm
  rw [CodingTheory.closeCodewordsRel_eq_setOf
    (ReedSolomon.code e.toEmbedding k)
    (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m)
    (bkr_radius_nonneg v m hvm)
    (bkrFiberCenter e.toEmbedding
      (bkrTransportedGraph m v hvm hfin pivot))]
  refine ⟨hcode, ?_⟩
  rw [hfloor]
  rw [hcardι] at hdist
  exact hdist

open scoped BigOperators in
noncomputable def rsSubspacePolynomial_monic
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (L : Submodule (ZMod 2) F) :
    (rsSubspacePolynomial L).Monic := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  change (∏ x : L, (Polynomial.X - Polynomial.C (x : F))).Monic
  simpa only using
    (Polynomial.monic_prod_X_sub_C (fun x : L => (x : F)) Finset.univ)

open scoped BigOperators in
noncomputable def rsSubspacePolynomial_natDegree
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] (L : Submodule (ZMod 2) F) :
    (rsSubspacePolynomial L).natDegree =
      2 ^ Module.finrank (ZMod 2) L := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  change (∏ x : L, (Polynomial.X - Polynomial.C (x : F))).natDegree =
    2 ^ Module.finrank (ZMod 2) L
  calc
    (∏ x : L, (Polynomial.X - Polynomial.C (x : F))).natDegree =
        (Finset.univ : Finset L).card := by
      exact Polynomial.natDegree_finset_prod_X_sub_C_eq_card Finset.univ
        (fun x : L => (x : F))
    _ = Fintype.card L := Finset.card_univ
    _ = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) L :=
      Module.card_eq_pow_finrank
    _ = 2 ^ Module.finrank (ZMod 2) L := by
      rw [ZMod.card]

noncomputable def rs_bkr_strict_extension_aux
    (m u v k : ℕ) (huv : u < v) (hvm : v ≤ m)
    (hsize : v ^ 2 ≤ (u + 1) * m) (hdeg : 2 ^ u < k) :
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {F : Type} [Field F] [Fintype F] [DecidableEq F],
      Fintype.card F = 2 ^ m → Fintype.card ι = 2 ^ m →
      ∃ (domain : ι ↪ F) (w : ι → F),
        2 ^ ((u + 1) * m - v ^ 2) ≤
          (_root_.ListDecodable.closeCodewordsRel
            ((ReedSolomon.code domain k : Set (ι → F))) w
            (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m)).ncard := by
  intro ι _ _ _ F _ _ _ hF hι
  classical
  letI : CharP F 2 := finiteField_charTwo_charP m hF
  letI : Algebra (ZMod 2) F := finiteField_charTwo_algebra m hF
  have hfin : Module.finrank (ZMod 2) F = m :=
    finiteField_charTwo_finrank m hF
  let e : ι ≃ F := Fintype.equivOfCardEq (hι.trans hF.symm)
  obtain ⟨profile, hfiber⟩ :=
    bkr_exists_large_graph_profile m u v huv hvm hfin hF hsize
  have hfiber_pos :
      0 < (bkrGraphProfileFiber m u v hvm hfin profile).card := by
    exact lt_of_lt_of_le (pow_pos (by omega) _) hfiber
  obtain ⟨pivot, hpivot⟩ := Finset.card_pos.mp hfiber_pos
  let codeword :
      ((Fin v → ZMod 2) →ₗ[ZMod 2]
        (Fin (m - v) → ZMod 2)) → (ι → F) :=
    fun f => bkrFiberCodeword e.toEmbedding
      (bkrTransportedGraph m v hvm hfin pivot)
      (bkrTransportedGraph m v hvm hfin f)
  let target : Set (ι → F) :=
    _root_.ListDecodable.closeCodewordsRel
      ((ReedSolomon.code e.toEmbedding k : Set (ι → F)))
      (bkrFiberCenter e.toEmbedding
        (bkrTransportedGraph m v hvm hfin pivot))
      (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m)
  have hpivot_profile :
      bkrGraphCoefficientProfile m u v hvm hfin pivot = profile := by
    simpa only [bkrGraphProfileFiber, Finset.mem_filter,
      Finset.mem_univ, true_and] using hpivot
  have hmaps : ∀ f ∈ bkrGraphProfileFiber m u v hvm hfin profile,
      codeword f ∈ target := by
    intro f hf
    have hf_profile :
        bkrGraphCoefficientProfile m u v hvm hfin f = profile := by
      simpa only [bkrGraphProfileFiber, Finset.mem_filter,
        Finset.mem_univ, true_and] using hf
    exact bkr_profile_fiber_codeword_mem_close e m u v k huv hvm hfin hι hdeg
      pivot f (hpivot_profile.trans hf_profile.symm)
  have hinj : Set.InjOn codeword
      (bkrGraphProfileFiber m u v hvm hfin profile : Set
        ((Fin v → ZMod 2) →ₗ[ZMod 2]
          (Fin (m - v) → ZMod 2))) := by
    intro f hf g hg hword
    have hf_profile :
        bkrGraphCoefficientProfile m u v hvm hfin f = profile := by
      simpa only [Finset.mem_coe, bkrGraphProfileFiber, Finset.mem_filter,
        Finset.mem_univ, true_and] using hf
    have hg_profile :
        bkrGraphCoefficientProfile m u v hvm hfin g = profile := by
      simpa only [Finset.mem_coe, bkrGraphProfileFiber, Finset.mem_filter,
        Finset.mem_univ, true_and] using hg
    exact bkr_profile_codeword_eq_imp_eq e m u v huv hvm hfin hF pivot f g
      (hf_profile.trans hg_profile.symm) hword
  have hcardle :
      (bkrGraphProfileFiber m u v hvm hfin profile : Set
        ((Fin v → ZMod 2) →ₗ[ZMod 2]
          (Fin (m - v) → ZMod 2))).ncard ≤ target.ncard := by
    exact Set.ncard_le_ncard_of_injOn codeword hmaps hinj (Set.toFinite target)
  refine ⟨e.toEmbedding,
    bkrFiberCenter e.toEmbedding
      (bkrTransportedGraph m v hvm hfin pivot), ?_⟩
  exact hfiber.trans (by
    simpa only [Set.ncard_coe_finset] using hcardle)

noncomputable def rs_lambda_bkr_fixed_loose
    (m U v k : ℕ) (hUv : U ≤ v) (hvm : v ≤ m)
    (hdeg : U = 0 ∨ 2 ^ (U - 1) < k) :
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {F : Type} [Field F] [Fintype F] [DecidableEq F],
      Fintype.card F = 2 ^ m → Fintype.card ι = 2 ^ m →
      ∃ (domain : ι ↪ F) (w : ι → F),
        2 ^ (m * U - v ^ 2) ≤
          (_root_.ListDecodable.closeCodewordsRel
            ((ReedSolomon.code domain k : Set (ι → F))) w
            (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m)).ncard := by
  intro ι _ _ _ F _ _ _ hF hι
  classical
  let e : ι ≃ F := Fintype.equivOfCardEq (hι.trans hF.symm)
  have hsingle :
      ∃ (domain : ι ↪ F) (w : ι → F),
        1 ≤ (_root_.ListDecodable.closeCodewordsRel
          ((ReedSolomon.code domain k : Set (ι → F))) w
          (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m)).ncard := by
    refine ⟨e.toEmbedding, 0, ?_⟩
    have hmem : (0 : ι → F) ∈
        _root_.ListDecodable.closeCodewordsRel
          ((ReedSolomon.code e.toEmbedding k : Set (ι → F))) 0
          (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m) := by
      rw [CodingTheory.closeCodewordsRel_eq_setOf
        (ReedSolomon.code e.toEmbedding k)
        (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m)
        (bkr_radius_nonneg v m hvm) 0]
      simp only [Set.mem_setOf_eq, zero_mem, hammingDist_self,
        Nat.zero_le, and_self]
    exact (Set.ncard_pos
      (s := _root_.ListDecodable.closeCodewordsRel
        ((ReedSolomon.code e.toEmbedding k : Set (ι → F))) 0
        (1 - (2 : ℝ) ^ v / (2 : ℝ) ^ m))).mpr ⟨0, hmem⟩
  by_cases hU0 : U = 0
  · subst U
    simpa only [Nat.mul_zero, Nat.zero_sub, pow_zero] using hsingle
  by_cases hsize : v ^ 2 ≤ m * U
  · have hdegree : 2 ^ (U - 1) < k := by
      rcases hdeg with h | h
      · exact False.elim (hU0 h)
      · exact h
    have huv' : U - 1 < v := by omega
    have hpred : U - 1 + 1 = U := by omega
    have hsize' : v ^ 2 ≤ ((U - 1) + 1) * m := by
      rw [hpred, Nat.mul_comm]
      exact hsize
    obtain ⟨domain, w, hw⟩ :=
      rs_bkr_strict_extension_aux m (U - 1) v k huv' hvm hsize' hdegree
        hF hι
    refine ⟨domain, w, ?_⟩
    simpa only [hpred, Nat.mul_comm U m] using hw
  · have hle : m * U ≤ v ^ 2 := by omega
    have hsub : m * U - v ^ 2 = 0 := Nat.sub_eq_zero_of_le hle
    simpa only [hsub, pow_zero] using hsingle

noncomputable def rs_lambda_superpoly_extension_easy
    (α β : ℝ) (hβ_lt : β < 1) (h_easy : α ≤ β ^ 2) :
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
  classical
  let qs : ℕ → ℕ := fun i => 2 ^ (i + 1)
  refine ⟨qs, ?_, ?_, ?_⟩
  · intro a b hab
    exact (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)) (by omega)
  · intro i
    rw [isPrimePow_nat_iff]
    exact ⟨2, i + 1, Nat.prime_two, by omega, rfl⟩
  · intro i ι _ _ _ F _ _ _ hF hι
    let e : ι ≃ F := Fintype.equivOfCardEq (hι.trans hF.symm)
    refine ⟨e.toEmbedding, 0, ?_⟩
    dsimp only
    let q : ℕ := qs i
    let k : ℕ := Nat.floor ((q : ℝ) ^ α)
    let δ : ℝ := 1 - (q : ℝ) ^ (β - 1)
    let C := ReedSolomon.code e.toEmbedding k
    have hq_pos : 0 < q := by
      dsimp [q, qs]
      positivity
    have hq_one : (1 : ℝ) ≤ q := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq_pos.ne')
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      have hp := Real.rpow_le_one_of_one_le_of_nonpos hq_one
        (show β - 1 ≤ 0 by linarith)
      linarith
    have hmem : (0 : ι → F) ∈ closeCodewordsRel ((C : Set (ι → F))) 0 δ := by
      rw [closeCodewordsRel_eq_setOf C δ hδ 0]
      simp only [Set.mem_setOf_eq, zero_mem, hammingDist_self, Nat.zero_le,
        and_self]
    have hone_nat :
        1 ≤ (closeCodewordsRel ((C : Set (ι → F))) 0 δ).ncard := by
      exact (Set.ncard_pos
        (s := closeCodewordsRel ((C : Set (ι → F))) 0 δ)).mpr ⟨0, hmem⟩
    have hone :
        (1 : ℝ) ≤ ((closeCodewordsRel ((C : Set (ι → F))) 0 δ).ncard : ℝ) := by
      exact_mod_cast hone_nat
    have hexp : (α - β ^ 2) * Real.logb 2 q ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h_easy)
        (Real.logb_nonneg (by norm_num) hq_one)
    have hrhs : (q : ℝ) ^ ((α - β ^ 2) * Real.logb 2 q) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq_one hexp
    exact hrhs.trans hone

noncomputable def rs_lambda_superpoly_extension_hard_of_parameters
    (α β : ℝ) (ms u v : ℕ → ℕ) (hms : StrictMono ms)
    (hparams : ∀ i, bkrLooseParameters α β (ms i) (u i) (v i)) :
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
            ((_root_.ListDecodable.closeCodewordsRel
              ((C : Set (ι → F))) w δ).ncard : ℝ) ≥
              (q : ℝ) ^ ((α - β ^ 2) * Real.logb 2 q) := by
  let qs : ℕ → ℕ := fun i => 2 ^ (ms i)
  refine ⟨qs, ?_, ?_, ?_⟩
  · intro a b hab
    exact (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)) (hms hab)
  · intro i
    rw [isPrimePow_nat_iff]
    exact ⟨2, ms i, Nat.prime_two, (hparams i).1, rfl⟩
  · intro i ι _ _ _ F _ _ _ hF hι
    obtain ⟨_hm, huv, hvm, hsize, hdeg, hradius, hexponent⟩ := hparams i
    let q : ℕ := qs i
    let k : ℕ := Nat.floor ((q : ℝ) ^ α)
    have hF' : Fintype.card F = 2 ^ (ms i) := by
      simpa only [q, qs] using hF
    have hι' : Fintype.card ι = 2 ^ (ms i) := by
      simpa only [q, qs] using hι
    have hdegree : 2 ^ (u i) < k := by
      simpa only [k, q, qs] using hdeg
    obtain ⟨domain, w, hbkr⟩ :=
      rs_bkr_strict_extension_aux (ms i) (u i) (v i) k huv hvm
        hsize hdegree hF' hι'
    refine ⟨domain, w, ?_⟩
    dsimp only
    let δ₀ : ℝ := 1 - (2 : ℝ) ^ (v i) / (2 : ℝ) ^ (ms i)
    let C := ReedSolomon.code domain k
    have hsubset :
        _root_.ListDecodable.closeCodewordsRel
            ((C : Set (ι → F))) w δ₀ ⊆
          _root_.ListDecodable.closeCodewordsRel
            ((C : Set (ι → F))) w (1 - (q : ℝ) ^ (β - 1)) := by
      exact _root_.ListDecodable.closeCodewordsRel_subset_of_le
        (by simpa only [δ₀, q, qs] using hradius) w
    have hncard :
        (_root_.ListDecodable.closeCodewordsRel
          ((C : Set (ι → F))) w δ₀).ncard ≤
        (_root_.ListDecodable.closeCodewordsRel
          ((C : Set (ι → F))) w (1 - (q : ℝ) ^ (β - 1))).ncard := by
      exact Set.ncard_le_ncard hsubset (Set.toFinite _)
    have hbkr_nat :
        2 ^ ((u i + 1) * ms i - (v i) ^ 2) ≤
          (_root_.ListDecodable.closeCodewordsRel
            ((C : Set (ι → F))) w δ₀).ncard := by
      simpa only [C, δ₀] using hbkr
    have hbkr' :
        ((2 ^ ((u i + 1) * ms i - (v i) ^ 2) : ℕ) : ℝ) ≤
          ((_root_.ListDecodable.closeCodewordsRel
            ((C : Set (ι → F))) w δ₀).ncard : ℝ) := by
      exact_mod_cast hbkr_nat
    have hncard' :
        ((2 ^ ((u i + 1) * ms i - (v i) ^ 2) : ℕ) : ℝ) ≤
          ((_root_.ListDecodable.closeCodewordsRel
            ((C : Set (ι → F))) w (1 - (q : ℝ) ^ (β - 1))).ncard : ℝ) := by
      exact hbkr'.trans (by exact_mod_cast hncard)
    have hexponent' :
        (q : ℝ) ^ ((α - β ^ 2) * Real.logb 2 q) ≤
          ((2 ^ ((u i + 1) * ms i - (v i) ^ 2) : ℕ) : ℝ) := by
      simpa only [q, qs, Real.rpow_natCast, Nat.cast_ofNat, Nat.cast_pow] using
        hexponent
    exact hexponent'.trans hncard'


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
  -- The finite coding-theory branch is complete. Use only the following top-level structure.
  -- 
  -- 1. Split on `α ≤ β ^ 2`. In that case exact `rs_lambda_superpoly_extension_easy α β _hβ_lt h_easy`.
  -- 
  -- 2. In the hard case set `hhard : β ^ 2 < α := lt_of_not_ge h_easy`. Prove two local arithmetic/dynamical claims.
  -- 
  -- Claim A (eventual arithmetic bridge):
  -- ```lean
  -- ∃ m₀, ∀ m ≥ m₀,
  --   bkrGoodRoundingWindow α β ε m →
  --   bkrLooseParameters α β m
  --     (Nat.ceil (α * (m : ℝ)) - 1)
  --     (Nat.ceil (β * (m : ℝ)))
  -- ```
  -- for each fixed ε>0 returned by Claim B. Write `U=ceil(αm)`, `V=ceil(βm)`, `A=U-αm`, `B=V-βm`. Use `Nat.ceil_mono`, `Nat.ceil_le`, `natCast_ceil_eq_intCast_ceil`, and `Int.ceil_sub_self_eq`. The exact identity
  -- `U*m - V^2 = (α-β^2)*m^2 + m*(A-2*β*B) - B^2`
  -- turns the good-window inequality into both `V^2 ≤ U*m` and the required exponent comparison. Here the strict BKR parameter is `u=U-1`, so `(u+1)*m=U*m`. The radius comparison follows from `β*m ≤ V` and `Real.rpow_le_rpow_of_exponent_le`. The degree bound has two branches: if A=B=0, then `αm=U` and `2^(U-1)<floor(2^U)`; otherwise `ε≤fract(αm)`, and for sufficiently large U, `2^(U-1)*(2^ε-1)>1`, which implies `2^(U-1)+1≤2^(αm)` and hence the strict floor inequality. Normalize the target exponent with `Real.logb_pow`, `Real.logb_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, and monotonicity of base-2 real powers.
  -- 
  -- Claim B (unbounded good windows):
  -- ```lean
  -- ∃ ε>0, ∀ N, ∃ m>N, bkrGoodRoundingWindow α β ε m
  -- ```
  -- Prove by the exhaustive rational-relation split. If α,β are rational, take arbitrarily large common-denominator multiples, so both errors vanish. If exactly one is rational, restrict to an arithmetic progression clearing its denominator and use one-dimensional irrational rotation (`AddCircle.denseRange_zsmul_coe_iff`) for the other coordinate. If both are irrational with an integer relation `p*α+q*β=r`, reduce the orbit to one dimension: for p>1 choose a fiber over β≈0 with nonzero α fractional part; for p=1 handle q≥1 and q≤-2 by approaching β fractional part 1 from below, while q=-1 contradicts `0<α<β<1`. If there is no integer relation among 1,α,β, prove dense range in `UnitAddTorus (Fin 2)` by the Weyl/Fourier method: geometric-series averages of every nonzero `UnitAddTorus.mFourier` tend to zero, extend via `UnitAddTorus.span_mFourier_closure_eq_top`, and contradict a continuous bump supported in a missed open rectangle. Target the rectangle `fract(αm)∈(1/4,1/2)` and `fract(βm)∈(7/8,1)`; then A>1/2 and B<1/8, so `2*β*B+B^2/m<A`. Use `mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples` and the frequently-atTop API to get hits above every N.
  -- 
  -- 3. After obtaining `⟨ε,hε,hhit⟩` and `⟨m₀,hbridge⟩`, apply
  -- `bkr_parameter_sequence_of_unbounded_windows α β ε m₀ hhit hbridge` to get `⟨ms,u,v,hms,hparams⟩`.
  -- 
  -- 4. Finish exactly with
  -- `rs_lambda_superpoly_extension_hard_of_parameters α β ms u v hms hparams`.
  -- 
  -- This avoids redoing any finite-field, polynomial, Reed–Solomon, radius-transfer, or cardinality work in the target. Do not request another fixed-parameter helper: both `rs_bkr_strict_extension_aux` and the complete hard assembly are now visible.
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

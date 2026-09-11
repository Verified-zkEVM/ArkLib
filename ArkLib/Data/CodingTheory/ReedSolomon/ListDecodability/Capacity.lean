/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.UniformRate
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.MathematicalUniformRate
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Bounds
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.FiniteField
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.GeometricBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Uniform
/-!
# Exact capacity lists at every rate

For the paper's all-rate capacity theorem, use `exists_rateCapacity_list`. It dispatches between
the certified first-order theorem at gaps at least `6/25` and the revised 300-based mathematical
construction at smaller gaps. Its explicit length and list bounds are
`rateCapacityLengthThreshold` and `rateCapacityListBound`.

## Which theorem should I use?

* `exists_rateCapacity_list` is the all-rate paper facade over prime fields with `q >= n`.
* `uniform_capacity_list_bound_300` exposes the revised small-gap parameters and the sharper
  arbitrary-field characteristic guard directly.
* `FirstOrder.firstOrderBranch_finiteLength_finiteSlack_bounds` and
  `FirstOrder.firstOrderBranch_finiteLength_rate_bounds` are the sharp first-derivative results;
  they live in `MutualCorrelatedAgreement/FirstOrder/Branchwise` because the same theorem proves
  both the complete-list and line-MCA bounds.
* `exists_capacity_list`, `capacityLengthThreshold`, and `CapacityListBounds` retain the earlier
  parameter family and its finite-field, quarter-gap, and half-gap refinements.

For the complete map from the paper's four quantitative regimes to their owner declarations, start
at `ReedSolomon/PaperGuide`.

This module assembles mathematical capacity list bounds for [DKTZ26].
`HasCapacityLists` spells out the common exact-list property. `CapacityListBounds` collects
the retained quantitative conclusions, led by a field-independent bound.
The capacity gap is fixed before the block length, dimension,
prime field, evaluation points, and received word. The statement includes both
field-size regimes and uses ordinary polynomial degree, including the zero polynomial.

This module proves list existence and cardinality. Mathematical finite-set specifications are in
`ReedSolomon/ListSpecification`; the physical coefficient-list contract is in
`ReedSolomon/ListDecoding/ExactOutput`. The same-output theorem and primitive-work ledger
for the retained exhaustive initial-jet executor are in
`ReedSolomon/ListDecoding/CapacityDecoderExecution`.

## Decoding procedure and formalization scope

The hidden-derivative algorithm chooses interpolation parameters and an ambient message dimension,
solves the homogeneous local-contact constraints for a nonzero differential polynomial, enumerates
its bounded-degree polynomial solutions by separant descent and regular Taylor lifting, and filters
by the original degree and agreement thresholds. The interpolation and solution-counting results
below justify the list bounds. The retained execution theorem enumerates initial jets and proves
an observed primitive-work bound. The symbolic replacement composes square-system solving with
Taylor-chart materialization and shared agreement recovery in `ListDecoding/SquareSystemDecoder`;
its torus isolated-root backend remains an explicit assumption. Neither execution interface makes
a bit-RAM complexity claim. Classical finite-set extraction here is not efficient enumeration.

## Decoding regimes

Capacity is the fixed-gap regime `1 - k / n - δ`, uniformly over all message dimensions.
This extends the low-rate hidden-derivative result of [BCPZZ26]. It is distinct from
unique decoding (`CodingTheory/BerlekampWelch`) and Johnson-radius interpolation
(`CodingTheory/GuruswamiSudan`). Those are separate developments, not assumptions here.
Field-independent geometric list bounds are in `ListDecodability/Capacity/GeometricBound`.
Mutual correlated agreement at capacity is in `MutualCorrelatedAgreement/Capacity`;
list cardinality and MCA are different properties.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], capacity list theorem.
* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed-Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], hidden-derivative interpolation.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon

open Polynomial

noncomputable section


/-! ## The paper-facing property and its quantitative instantiation

The property below separates the meaning of an exact capacity list from the numerical
bound one proves for it. Its bound argument can express several simultaneous estimates.
The current paper theorem `exists_rateCapacity_list` supplies the revised scalar bound.
The retained `exists_capacity_list` supplies `CapacityListBounds`, whose simultaneous estimates
apply to the same exact list, not to separately chosen candidate families.
-/

/-- Minimum block length: one at gaps at least `1/4`, and `8m` for smaller gaps.
Here `m = weightedSupportMultiplicity δ = ⌈100 d² H_(d-1)⌉`, where
`d = capacityDerivativeOrder δ` and `H_r = ∑_{i=1}^r 1/i` is the harmonic number.
In the small-gap regime, `d = ⌈exp(2.7 / δ)⌉`. The multiplicity formula is used
only in that regime; gaps at least `1/4` have length threshold one. -/
def capacityLengthThreshold (δ : ℝ) : ℕ :=
  if (1 / 4 : ℝ) ≤ δ then 1 else 8 * weightedSupportMultiplicity δ

/-- Field-independent list bound. At small gaps it is `4m²(4m/δ)^d n^d`;
at gaps at least `1/4` we use `n`, with strict inequality proved separately.
The derivative order `d` and multiplicity `m` depend only on the gap. -/
def capacityListBound (δ : ℝ) (n : ℕ) : ℝ :=
  if (1 / 4 : ℝ) ≤ δ then n else
    4 * (weightedSupportMultiplicity δ : ℝ) ^ 2 *
      (4 * weightedSupportMultiplicity δ / δ) ^ capacityDerivativeOrder δ *
      n ^ capacityDerivativeOrder δ

/-- Exact list decodability at a fixed gap, uniformly over prime fields and code rates.

In the paper's notation, `n` is the block length, `k` the message dimension, `q` the prime
alphabet size, and `A` the number of required agreements. Thus `A ≥ k + δn` means agreement
fraction at least `k/n + δ`, or relative error at most `1 - k/n - δ`. The lower bound `N`
and cardinality rule are chosen before all four code parameters and the received word.

`bounds n k q A ℓ` is a property of the list cardinality `ℓ`; it is not an assumption
on the received word. Supplying a different bound does not change the exact-list contract.
The biconditional below specifies the entire list, including zero whenever it qualifies.
This is a mathematical property, with no executable algorithm or cost model. -/
def HasCapacityLists (δ : ℝ) (N : ℕ)
    (bounds : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  -- The gap and length threshold are fixed before all code parameters.
  ∀ n k q A : ℕ,
    N ≤ n →
    --
    -- Dimension k means degree strictly below k; the rate is k/n.
    0 < k → k ≤ n →
    --
    -- The alphabet is the prime field 𝔽_q, large enough for n distinct points.
    q.Prime → n ≤ q →
    --
    -- Agreement A ≥ k + δn is the capacity-gap decoding condition.
    -- The retained interface allows thresholds up to 2n, even when impossible.
    (k : ℝ) + δ * n ≤ A → A ≤ 2 * n →
    --
    -- `↪` asserts distinct evaluation points; the received word is arbitrary.
    ∀ (α : Fin n ↪ ZMod q) (y : Fin n → ZMod q),
      ∃ list : Finset (Polynomial (ZMod q)),
        --
        -- Exactly all qualifying polynomials: both completeness and exclusion
        -- of spurious candidates. Polynomial.degree includes the zero polynomial.
        (∀ P, P ∈ list ↔
          P.degree < k ∧ A ≤ Code.agree (fun i => P.eval (α i)) y) ∧
        --
        -- Impossible agreement thresholds return the empty mathematical list.
        (n < A → list = ∅) ∧
        --
        -- The specified estimates hold for this very list's cardinality.
        bounds n k q A list.card

/-- Any pointwise consequence of the cardinality estimates holds for the same exact lists.
This lets a consumer retain only the estimate it needs, without redoing list extraction. -/
theorem HasCapacityLists.mono {δ : ℝ} {N : ℕ}
    {bounds bounds' : ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    (h : HasCapacityLists δ N bounds)
    (hbound : ∀ n k q A ℓ, bounds n k q A ℓ → bounds' n k q A ℓ) :
    HasCapacityLists δ N bounds' := by
  intro n k q A hn hk hkn hq hnq hA hAn α y
  obtain ⟨list, hexact, hempty, hb⟩ := h n k q A hn hk hkn hq hnq hA hAn α y
  exact ⟨list, hexact, hempty, hbound n k q A list.card hb⟩

/-- The simultaneous list bounds for the retained parameter family.
The field-independent estimate leads; field-dependent estimates remain useful when
their constants give a smaller value. All bounds refer to the same cardinality `ℓ`. -/
structure CapacityListBounds (δ : ℝ) (n k q A ℓ : ℕ) : Prop where
  -- The headline estimate: polynomial in block length, independently of q.
  fieldIndependent : (ℓ : ℝ) ≤ capacityListBound δ n

  -- Large gaps admit stronger statements: fewer than n candidates, then uniqueness.
  quarterGap : (1 / 4 : ℝ) ≤ δ → ℓ < n
  halfGap : (1 / 2 : ℝ) ≤ δ → ℓ ≤ 1

  -- At small gaps, finite-field root counting also gives 4m q^(2d).
  finiteField : δ < (1 / 4 : ℝ) →
    ℓ ≤ 4 * weightedSupportMultiplicity δ * q ^ (2 * capacityDerivativeOrder δ)

  -- A larger field improves this to 4m q^d. With K = max{k, ⌊δn/2⌋},
  -- truncated natural subtraction expresses q ≥ 2 max{0, mA - K + d}.
  largeField : δ < (1 / 4 : ℝ) →
    2 * (weightedSupportMultiplicity δ * A + capacityDerivativeOrder δ -
      max k ⌊δ * (n : ℝ) / 2⌋₊) ≤ q →
    ℓ ≤ 4 * weightedSupportMultiplicity δ * q ^ capacityDerivativeOrder δ

/-- **Uniform first-order capacity lists from gap `6/25`.**  The squarefree-product
certificate represents the exact list by at most `307 n` polynomials.  The threshold
`n ≥ 23`, together with `n ≤ q`, supplies precisely the positive-characteristic condition
`max (k - 1) 4 < q` when `k ≥ 2`; the elementary `k = 1` branch is characteristic-free.

This is a mathematical list theorem.  It does not change the derivative order, multiplicity,
or runtime regimes of the executable capacity decoder. -/
theorem uniformFirstOrder_capacity_list (δ : ℝ) (hδ : (6 / 25 : ℝ) ≤ δ) :
    HasCapacityLists δ 23 (fun n _k _q _A ℓ ↦ ℓ ≤ 307 * n) := by
  classical
  intro n k q A hn hk hkn hq hnq hgap _hAupper domain received
  by_cases hAn : A ≤ n
  · let _ : Fact q.Prime := ⟨hq⟩
    have hgapUniform : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A := by
      have hnnonneg : (0 : ℝ) ≤ n := by positivity
      have hmul := mul_le_mul_of_nonneg_right hδ hnnonneg
      linarith
    have hchar : 2 ≤ k →
        ringChar (ZMod q) = 0 ∨ max (k - 1) 4 < ringChar (ZMod q) := by
      intro hkTwo
      right
      rw [ringChar.eq (ZMod q) q]
      have hn23 : 23 ≤ n := hn
      omega
    obtain ⟨list, hlist, hcard⟩ :=
      exists_uniformFirstOrder_list n k A domain received
        (by omega) hk hAn hgapUniform hchar
    refine ⟨list, ?_, ?_, hcard⟩
    · intro P
      rw [hlist]
      simp only [closePolynomialSet]
      simp [polynomialAgreementSet, Code.agree]
    · intro hover
      exact (Nat.not_lt_of_ge hAn hover).elim
  · refine ⟨∅, ?_, fun _ ↦ rfl, by simp⟩
    intro P
    constructor
    · intro hmem
      simp at hmem
    · rintro ⟨_hdegree, hagree⟩
      exfalso
      apply hAn
      have hcard := Code.agree_le_card
        (u := fun i ↦ P.eval (domain i)) (v := received)
      exact hagree.trans (by simpa using hcard)

/-- **Capacity lists at every rate, with all prescribed list bounds.**

Fix any gap `0 < δ < 1`. The threshold, derivative order, and multiplicity depend only
on that gap. `HasCapacityLists` gives the exact agreement list for every admissible code
and received word; `CapacityListBounds` gives the field-independent bound and both
finite-field refinements, together with the quarter-gap and half-gap conclusions.

This retains the earlier parameter family; use `exists_rateCapacity_list` for the current paper.
It does not certify the separate decoder or running-time assertion. -/
theorem exists_capacity_list (δ : ℝ) (hδ : 0 < δ) (hδ_one : δ < 1) :
    HasCapacityLists δ (capacityLengthThreshold δ) (CapacityListBounds δ) := by
  classical
  intro n k q A hn hk hkn hq hnq hA hAn α y
  obtain ⟨list, hexact, hempty, hhalf, hquarter, hsmall⟩ :=
    exists_field_bounded_capacity_list δ hδ hδ_one n k q A hn hk hkn hq hnq hA hAn α y
  refine ⟨list, hexact, hempty, ?_, hquarter, hhalf, ?_, ?_⟩
  · by_cases hlarge : (1 / 4 : ℝ) ≤ δ
    · simpa only [capacityListBound, if_pos hlarge] using
        (show (list.card : ℝ) ≤ n by exact_mod_cast (hquarter hlarge).le)
    · have hδsmall := lt_of_not_ge hlarge
      by_cases hover : n < A
      · rw [hempty hover, Finset.card_empty, Nat.cast_zero]
        unfold capacityListBound
        positivity
      · let : Fact q.Prime := ⟨hq⟩
        have hthreshold := (agreementThreshold_le_iff_real hδ.le n k A).mpr hA
        have hblock : 8 * weightedSupportMultiplicity δ ≤ n := by
          simpa only [capacityLengthThreshold, if_neg hlarge] using hn
        have hgeom := prescribed_geometric_finite_list_bound δ n k α y hδ hδsmall hk
          (by simpa only [weightedSupportMultiplicity, capacityDerivativeOrder, if_neg hlarge]
            using hblock)
          (hthreshold.trans (Nat.le_of_not_gt hover))
          (Or.inr (by simpa only [ringChar.eq (ZMod q) q] using hnq)) list (by
            intro P hP
            have hp := (hexact P).mp hP
            refine ⟨hp.1, ?_⟩
            convert hthreshold.trans hp.2 using 1 <;> try rfl
            unfold Code.agree
            congr 1
            ext i
            simp)
        simpa only [capacityListBound, weightedSupportMultiplicity, capacityDerivativeOrder,
          if_neg hlarge] using hgeom
  · intro hs
    exact (hsmall hs).1
  · intro hs
    exact (hsmall hs).2

/-- A sufficient all-rate block threshold `N(δ)` for the paper's capacity result.

For `δ ≥ 6/25`, this facade selects `n ≥ 23`; no minimality is asserted.
For `0 < δ < 6/25`, put
`d = ⌈exp(3/(2δ))⌉`, `m = ⌈300 d² log(6d)⌉`, and `ν = ⌈m/δ²⌉ - 1 = Bjet(δ)`.
The threshold is then `ν + 1 = ⌈m/δ²⌉`. In particular, `n ≥ N(δ)` and prime `q ≥ n`
give `ν < q`, the jet-degree part of the small-gap characteristic guard.
These parameters depend only on `δ`, uniformly over all code rates. -/
def rateCapacityLengthThreshold (δ : ℝ) : ℕ :=
  -- The large-gap certificate uses only the first derivative.
  if (6 / 25 : ℝ) ≤ δ then 23 else
    -- The strict total-jet cap Bjet(δ) plus one in the higher-order branch.
    HiddenDerivative.uniformRatePartitionMathematicalLength δ

/-- The paper's complete-list bound `L_δ(n)`, independent of the alphabet size.

For `δ ≥ 6/25`, this is `307 n`. For `0 < δ < 6/25`, it is `ν² (2ν/δ)^d n^d`, with
`d = ⌈exp(3/(2δ))⌉` and `ν = Bjet(δ)` as in `rateCapacityLengthThreshold`. Thus the
small-gap coefficient and exponent depend only on the gap; neither depends on `k` or `q`.
This is a cardinality bound, separate from the cost of producing the list. -/
def rateCapacityListBound (δ : ℝ) (n : ℕ) : ℝ :=
  if (6 / 25 : ℝ) ≤ δ then 307 * n else
    -- Squarefree differential-root counting contributes ν² and the d-th power.
    (HiddenDerivative.uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
      (2 * HiddenDerivative.uniformRatePartitionMathematicalJetBound δ / δ) ^
        HiddenDerivative.uniformRatePartitionOrder δ *
      n ^ HiddenDerivative.uniformRatePartitionOrder δ

/-- **All-rate exact capacity lists for the paper's revised parameter family.**

This is the list-decoding part of the paper's gap-from-capacity result. Fix `δ > 0` first.
For every `n ≥ N(δ)`, `1 ≤ k ≤ n`, prime `q ≥ n`, injective evaluation map into `𝔽_q`, and
received word, the complete list at agreement threshold `A ≥ k + δn` has at most `L_δ(n)`
members. There is no randomness or genericity assumption on the evaluation set.

The two parameter regimes, spelled out in `rateCapacityLengthThreshold` and
`rateCapacityListBound`, are:

* `δ ≥ 6/25`: `N(δ) = 23` and `L_δ(n) = 307 n` (the first-order certificate).
* `0 < δ < 6/25`: `d = ⌈exp(3/(2δ))⌉`, `m = ⌈300 d² log(6d)⌉`,
  `ν = ⌈m/δ²⌉ - 1`, `N(δ) = ν + 1`, and `L_δ(n) = ν² (2ν/δ)^d n^d`.

All these choices precede `n, k, q, A` and the received word. The prime-field assumption and
length cutoff supply the characteristic conditions internally. For the stronger arbitrary-field
small-gap statement with an explicit characteristic premise, use
`uniform_capacity_list_bound_300`.

Expand `HasCapacityLists` to read the exact membership biconditional: degree strictly below `k`
and at least `A` agreements, including zero. Its interface allows `A ≤ 2n`; when `A > n`,
the list is empty. No upper bound on `δ` is needed, since impossible agreement requirements are
handled this way. This theorem proves existence and size; executable decoder correctness and
runtime are separate claims. -/
theorem exists_rateCapacity_list
    -- Fix the capacity gap before choosing any code or received word.
    (δ : ℝ) (hδ : 0 < δ) :
    -- The property below universally quantifies n, k, prime q ≥ n, A, domain, and word.
    -- It returns a finset with exact membership, not merely a containing candidate list.
    HasCapacityLists δ (rateCapacityLengthThreshold δ)
      -- The ignored arguments are k, q, A: the bound depends only on δ and n.
      (fun n _ _ _ card => (card : ℝ) ≤ rateCapacityListBound δ n) := by
  classical
  by_cases hlarge : (6 / 25 : ℝ) ≤ δ
  · have h := uniformFirstOrder_capacity_list δ hlarge
    simpa only [rateCapacityLengthThreshold, if_pos hlarge] using h.mono
      (fun n _ _ _ card hb ↦ by
        simpa only [rateCapacityListBound, if_pos hlarge, Nat.cast_mul, Nat.cast_ofNat] using
          (show (card : ℝ) ≤ 307 * n by exact_mod_cast hb))
  · intro n k q A hn hk _hkn hq hnq hgap _hAupper domain received
    let _ : Fact q.Prime := ⟨hq⟩
    by_cases hAn : A ≤ n
    · have hn' : HiddenDerivative.uniformRatePartitionMathematicalLength δ ≤ n := by
        simpa only [rateCapacityLengthThreshold, if_neg hlarge] using hn
      obtain ⟨hf, hb⟩ := mathematicalUniformRatePartition_close_list_bound_of_length_characteristic
        hδ (lt_of_not_ge hlarge)
        hn' hk hgap hAn domain received (Or.inr (by
          simpa only [ringChar.eq (ZMod q) q] using hnq))
      refine ⟨hf.toFinset, ?_, ?_, ?_⟩
      · intro P
        simp only [Set.Finite.mem_toFinset, closePolynomialSet]
        simp only [polynomialAgreementSet, Code.agree, Set.mem_ofPred_eq, and_congr_right_iff]
        intro _
        constructor <;> intro h <;> convert h using 1 <;> congr 1 <;> ext i <;> simp
      · intro hover
        exact (Nat.not_lt_of_ge hAn hover).elim
      · rw [Set.ncard_eq_toFinset_card _ hf] at hb
        simpa only [rateCapacityListBound, if_neg hlarge] using hb
    · refine ⟨∅, ?_, fun _ ↦ rfl, ?_⟩
      · intro P
        constructor
        · intro hmem
          simp at hmem
        · rintro ⟨_, hagree⟩
          exfalso
          apply hAn
          have hc := Code.agree_le_card (u := fun i ↦ P.eval (domain i)) (v := received)
          exact hagree.trans (by simpa using hc)
      · simp only [Finset.card_empty, Nat.cast_zero, rateCapacityListBound, if_neg hlarge]
        positivity


end

end ReedSolomon

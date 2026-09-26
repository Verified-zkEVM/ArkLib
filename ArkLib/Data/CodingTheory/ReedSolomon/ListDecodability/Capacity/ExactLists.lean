/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.MathematicalUniformRate
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.FiniteField
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.GeometricBound
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Uniform

/-!
# Exact capacity lists at every rate

Fix a capacity gap `δ > 0`. `HasCapacityLists δ N bounds` states that for every block length
`n ≥ N`, message dimension `1 ≤ k ≤ n`, prime `q ≥ n`, agreement threshold `A ≥ k + δ n`,
injective evaluation map into `ZMod q` and received word, there is a finite set containing exactly
the polynomials of degree below `k` with at least `A` agreements, empty when `n < A`, whose
cardinality satisfies `bounds n k q A`. The threshold `N` and the bound are chosen before the code
and the received word, uniformly over all rates.

Two families instantiate it.

* `exists_rateCapacity_list`: for `δ ≥ 6/25`, `N = 23` and at most `307 n` members, from the
  uniform first-order certificate; for `0 < δ < 6/25`, the mathematical uniform length threshold
  and at most `C n^d` members, with `d = ⌈exp (3/(2δ))⌉₊`.
* `exists_capacity_list`: the weighted-support parameters, with the simultaneous estimates
  `CapacityListBounds`: a field-independent bound, the quarter-gap and half-gap bounds, and two
  finite-field bounds.

## Main statements

* `ReedSolomon.HasCapacityLists`: exact capacity lists with a cardinality predicate.
* `ReedSolomon.uniformFirstOrder_capacity_list`: lists of at most `307 n` members at gaps at least
  `6/25`.
* `ReedSolomon.exists_rateCapacity_list`: lists of at most `rateCapacityListBound δ n` members at
  every positive gap.
* `ReedSolomon.exists_capacity_list`: lists satisfying `CapacityListBounds` at every positive gap.

## References

* [DKTZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative HiddenDerivative.RatePartition

noncomputable section

/-- The weighted-support block-length threshold: `1` at gaps at least `1/4`, and `8m` below,
where `m = weightedSupportMultiplicity d` and `d = capacityDerivativeOrder δ`. -/
def capacityLengthThreshold (δ : ℝ) : ℕ :=
  if (1 / 4 : ℝ) ≤ δ then 1 else 8 * weightedSupportMultiplicity (capacityDerivativeOrder δ)

/-- The field-independent weighted-support list bound: `n` at gaps at least `1/4`, and
`4m² (4m/δ)^d n^d` below, with `d = capacityDerivativeOrder δ` and
`m = weightedSupportMultiplicity d`. -/
def capacityListBound (δ : ℝ) (n : ℕ) : ℝ :=
  if (1 / 4 : ℝ) ≤ δ then n else
    4 * (weightedSupportMultiplicity (capacityDerivativeOrder δ) : ℝ) ^ 2 *
      (4 * weightedSupportMultiplicity (capacityDerivativeOrder δ) / δ) ^
        capacityDerivativeOrder δ *
      n ^ capacityDerivativeOrder δ

/-- **Exact capacity lists.** For every `n ≥ N`, `1 ≤ k ≤ n`, prime `q ≥ n`, `A ≥ k + δ n`,
injective evaluation map `α : Fin n ↪ ZMod q` and received word `y`, some finite set contains
exactly the polynomials of degree below `k` agreeing with `y` in at least `A` coordinates, is empty
when `n < A`, and has cardinality `ℓ` with `bounds n k q A ℓ`. -/
def HasCapacityLists (δ : ℝ) (N : ℕ) (bounds : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ n k q A : ℕ, N ≤ n → 0 < k → k ≤ n → q.Prime → n ≤ q → (k : ℝ) + δ * n ≤ A →
    ∀ (α : Fin n ↪ ZMod q) (y : Fin n → ZMod q),
      ∃ list : Finset (Polynomial (ZMod q)),
        (∀ P, P ∈ list ↔ P.degree < k ∧ A ≤ Code.agree (fun i => P.eval (α i)) y) ∧
        (n < A → list = ∅) ∧
        bounds n k q A list.card

/-- A pointwise weaker cardinality predicate holds for the same exact lists. -/
theorem HasCapacityLists.mono {δ : ℝ} {N : ℕ}
    {bounds bounds' : ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    (h : HasCapacityLists δ N bounds)
    (hbound : ∀ n k q A ℓ, bounds n k q A ℓ → bounds' n k q A ℓ) :
    HasCapacityLists δ N bounds' := by
  intro n k q A hn hk hkn hq hnq hA α y
  obtain ⟨list, hexact, hempty, hb⟩ := h n k q A hn hk hkn hq hnq hA α y
  exact ⟨list, hexact, hempty, hbound n k q A list.card hb⟩

/-- The simultaneous weighted-support estimates for a list of cardinality `ℓ`, with
`d = capacityDerivativeOrder δ` and `m = weightedSupportMultiplicity d`. -/
structure CapacityListBounds (δ : ℝ) (n k q A ℓ : ℕ) : Prop where
  /-- The field-independent bound `capacityListBound δ n`. -/
  fieldIndependent : (ℓ : ℝ) ≤ capacityListBound δ n
  /-- At gaps at least `1/4`, fewer than `n` members. -/
  quarterGap : (1 / 4 : ℝ) ≤ δ → ℓ < n
  /-- At gaps at least `1/2`, at most one member. -/
  halfGap : (1 / 2 : ℝ) ≤ δ → ℓ ≤ 1
  /-- Below gap `1/4`, at most `4m q^(2d)` members. -/
  finiteField : δ < (1 / 4 : ℝ) →
    ℓ ≤ 4 * weightedSupportMultiplicity (capacityDerivativeOrder δ) *
      q ^ (2 * capacityDerivativeOrder δ)
  /-- Below gap `1/4`, at most `4m q^d` members when `q ≥ 2 (m A + d - max k ⌊δ n / 2⌋₊)`. -/
  largeField : δ < (1 / 4 : ℝ) →
    2 * (weightedSupportMultiplicity (capacityDerivativeOrder δ) * A +
      capacityDerivativeOrder δ - max k ⌊δ * (n : ℝ) / 2⌋₊) ≤ q →
    ℓ ≤ 4 * weightedSupportMultiplicity (capacityDerivativeOrder δ) *
      q ^ capacityDerivativeOrder δ

/-- Over a prime field `ZMod q`, membership in the complete agreement list with classical
decidable equality is agreement in the sense of `Code.agree`. -/
private theorem mem_classical_closePolynomialSet_zmod_iff {q n k A : ℕ} [Fact q.Prime]
    (α : Fin n ↪ ZMod q) (y : Fin n → ZMod q) (P : Polynomial (ZMod q)) :
    P ∈ @closePolynomialSet _ _ (fun a b ↦ Classical.propDecidable (a = b)) n α y k A ↔
      P.degree < k ∧ A ≤ Code.agree (fun i => P.eval (α i)) y := by
  rw [show (fun a b : ZMod q ↦ Classical.propDecidable (a = b)) = ZMod.decidableEq q from
    Subsingleton.elim _ _]
  rfl

/-- Over a prime field, an empty list is the exact list at any threshold `A > n`. -/
private theorem capacity_list_empty_of_lt {q n k A : ℕ} (hAn : ¬ A ≤ n)
    (α : Fin n ↪ ZMod q) (y : Fin n → ZMod q) (P : Polynomial (ZMod q)) :
    P ∈ (∅ : Finset (Polynomial (ZMod q))) ↔
      P.degree < k ∧ A ≤ Code.agree (fun i => P.eval (α i)) y := by
  simp only [Finset.notMem_empty, false_iff, not_and]
  intro _ hagree
  have hcard := Code.agree_le_card (u := fun i ↦ P.eval (α i)) (v := y)
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Uniform first-order capacity lists.** At every gap `δ ≥ 6/25`, exact capacity lists exist
from block length `23` with at most `307 n` members. -/
theorem uniformFirstOrder_capacity_list (δ : ℝ) (hδ : (6 / 25 : ℝ) ≤ δ) :
    HasCapacityLists δ 23 (fun n _k _q _A ℓ ↦ ℓ ≤ 307 * n) := by
  intro n k q A hn hk hkn hq hnq hgap domain received
  by_cases hAn : A ≤ n
  · let _ : Fact q.Prime := ⟨hq⟩
    have hgapUniform : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A := by
      nlinarith [mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hchar : 2 ≤ k → ringChar (ZMod q) = 0 ∨ k - 1 < ringChar (ZMod q) := by
      intro _
      right
      rw [ringChar.eq (ZMod q) q]
      omega
    obtain ⟨list, hlist, hcard⟩ :=
      exists_uniformFirstOrder_list n k A domain received (by omega) hk hAn hgapUniform hchar
    refine ⟨list, hlist, ?_, hcard⟩
    exact fun hover ↦ absurd hAn (by omega)
  · exact ⟨∅, capacity_list_empty_of_lt hAn domain received, fun _ ↦ rfl, by simp⟩

/-- **Weighted-support capacity lists.** At every gap `δ > 0`, exact capacity lists exist from
block length `capacityLengthThreshold δ` and satisfy all the estimates of `CapacityListBounds`. -/
theorem exists_capacity_list (δ : ℝ) (hδ : 0 < δ) :
    HasCapacityLists δ (capacityLengthThreshold δ) (CapacityListBounds δ) := by
  intro n k q A hn hk hkn hq hnq hA α y
  obtain ⟨list, hexact, hempty, hhalf, hquarter, hsmall⟩ :=
    exists_field_bounded_capacity_list δ hδ n k q A hn hk hkn hq hnq hA α y
  refine ⟨list, hexact, hempty, ?_, hquarter, hhalf, fun hs ↦ (hsmall hs).1,
    fun hs ↦ (hsmall hs).2⟩
  by_cases hlarge : (1 / 4 : ℝ) ≤ δ
  · simpa only [capacityListBound, ite_eq_left hlarge] using
      (show (list.card : ℝ) ≤ n by exact_mod_cast (hquarter hlarge).le)
  have hδsmall := lt_of_not_ge hlarge
  by_cases hover : n < A
  · rw [hempty hover, Finset.card_empty, Nat.cast_zero]
    unfold capacityListBound
    positivity
  let _ : Fact q.Prime := ⟨hq⟩
  have hthreshold := (capacityAgreementThreshold_le_iff_real hδ.le n k A).mpr hA
  have hblock : 8 * weightedSupportMultiplicity (capacityDerivativeOrder δ) ≤ n := by
    simpa only [capacityLengthThreshold, ite_eq_right hlarge] using hn
  have hgeom := prescribed_geometric_finite_list_bound δ n k α y hδ hδsmall hk
    (by simpa only [weightedSupportMultiplicity, capacityDerivativeOrder_eq_ceil hδsmall]
      using hblock)
    (hthreshold.trans (Nat.le_of_not_gt hover))
    (Or.inr (by simpa only [ringChar.eq (ZMod q) q] using hnq)) list (by
      intro P hP
      have hp := (hexact P).mp hP
      classical
      refine ⟨hp.1, ?_⟩
      convert hthreshold.trans hp.2 using 1
      simp only [polynomialAgreementSet, Code.agree]
      congr 1
      ext i
      simp)
  simpa only [capacityListBound, weightedSupportMultiplicity,
    capacityDerivativeOrder_eq_ceil hδsmall, ite_eq_right hlarge] using hgeom

/-- The all-rate block-length threshold: `23` at gaps at least `6/25`, and
`uniformMathematicalCapacityLength δ` below. -/
def rateCapacityLengthThreshold (δ : ℝ) : ℕ :=
  if (6 / 25 : ℝ) ≤ δ then 23 else uniformMathematicalCapacityLength δ

/-- The all-rate list bound: `307 n` at gaps at least `6/25`, and
`mathematicalUniformListConstant δ * n^d` below, with `d = uniformDerivativeOrder δ`. -/
def rateCapacityListBound (δ : ℝ) (n : ℕ) : ℝ :=
  if (6 / 25 : ℝ) ≤ δ then 307 * n else
    mathematicalUniformListConstant δ * n ^ uniformDerivativeOrder δ

/-- **Capacity lists at every rate.** At every gap `δ > 0`, exact capacity lists exist from block
length `rateCapacityLengthThreshold δ` with at most `rateCapacityListBound δ n` members; both
depend only on `δ`, and the bound does not depend on `k`, `q` or `A`. -/
theorem exists_rateCapacity_list (δ : ℝ) (hδ : 0 < δ) :
    HasCapacityLists δ (rateCapacityLengthThreshold δ)
      (fun n _ _ _ ℓ => (ℓ : ℝ) ≤ rateCapacityListBound δ n) := by
  by_cases hlarge : (6 / 25 : ℝ) ≤ δ
  · simpa only [rateCapacityLengthThreshold, ite_eq_left hlarge] using
      (uniformFirstOrder_capacity_list δ hlarge).mono fun n _ _ _ ℓ hb ↦ by
        simpa only [rateCapacityListBound, ite_eq_left hlarge] using
          (show (ℓ : ℝ) ≤ 307 * n by exact_mod_cast hb)
  intro n k q A hn hk hkn hq hnq hgap domain received
  by_cases hAn : A ≤ n
  · let _ : Fact q.Prime := ⟨hq⟩
    have hn' : uniformMathematicalCapacityLength δ ≤ n := by
      simpa only [rateCapacityLengthThreshold, ite_eq_right hlarge] using hn
    have hchar : ringChar (ZMod q) = 0 ∨ k - 1 < ringChar (ZMod q) := by
      right
      rw [ringChar.eq (ZMod q) q]
      omega
    obtain ⟨hf, hb⟩ := mathematicalUniform_capacity_list_bound δ hδ (lt_of_not_ge hlarge)
      n k A hn' hk hgap hAn domain received hchar
    refine ⟨hf.toFinset, fun P ↦ hf.mem_toFinset.trans
      (mem_classical_closePolynomialSet_zmod_iff _ _ P),
      fun hover ↦ absurd hAn (by omega), ?_⟩
    rw [Set.ncard_eq_toFinset_card _ hf] at hb
    simpa only [rateCapacityListBound, ite_eq_right hlarge] using hb
  · refine ⟨∅, capacity_list_empty_of_lt hAn domain received, fun _ ↦ rfl, ?_⟩
    simp only [Finset.card_empty, Nat.cast_zero, rateCapacityListBound, ite_eq_right hlarge]
    exact mul_nonneg ((by positivity : (0 : ℝ) ≤ 4 / (3 * δ)).trans (le_max_right _ _))
      (by positivity)

end

end ReedSolomon

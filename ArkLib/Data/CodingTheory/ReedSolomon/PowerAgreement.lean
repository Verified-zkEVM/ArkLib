/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
public import ArkLib.Data.Polynomial.SpecializationAvoidance
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact power agreement for Reed–Solomon codes

A tuple `w : Fin (ℓ + 1) → ι → F` of received words is batched by one challenge `z` into
`i ↦ ∑ t, z ^ t * w t i`. A polynomial `Q` of degree below `k` close to the batched word has
*exact power agreement* if `Q = ∑ t, z ^ t • P t` for polynomials `P t` of degree below `k`, and
the coordinates where `Q` agrees with the batched word are exactly the coordinates where every
`P t` agrees with `w t`. This file states that property and its uniform version in polynomial
form, and identifies them with the code-level predicates `Code.HasExactAgreement` and
`Code.UniformExactAgreement` for the Reed–Solomon code and the batching map
`CoreDefinitions.univariatePowersGenerator F ℓ`.

The identification needs no relation between `k` and the agreement threshold or the block
length. Codeword witnesses give polynomial witnesses whose evaluations are correct; if `k`
exceeds the number of evaluation points, the polynomial identity `Q = ∑ t, z ^ t • P t` can
still fail, and it is repaired by adding the difference to `P 0`, whose weight is `z ^ 0 = 1`
(`exists_powerBatchedPolynomial_eq`).

For a fixed tuple `P`, the discrepancy at a coordinate `i` is a polynomial of degree at most `ℓ`
in the challenge, `curveDiscrepancy domain w P i`, whose coefficients are the constituent
discrepancies `(P t).eval (domain i) - w t i`. It is zero exactly at the common agreements, so
outside the roots of the nonzero discrepancies, at most `ℓ * (|ι| - L)` challenges when the tuple
has `L` common agreements, the batched polynomial gains no extra agreement. Exact power agreement
over an extension field descends to the base field with the same number of exceptional
challenges.

The code-level characterizations let the counting and transfer theorems of
`ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement` apply to Reed–Solomon statements. The
interleaved statements are in `ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement`.

## Main definitions

* `ReedSolomon.powerBatchedWord`, `ReedSolomon.powerBatchedPolynomial`: batching of received
  words and of message polynomials.
* `ReedSolomon.commonCurveAgreementSet`: coordinates where every `P t` agrees with `w t`.
* `ReedSolomon.polynomialTupleFamily`: the interpolant tuples on `k`-element samples.
* `ReedSolomon.powerBatchedCoordinate`: a coordinate vector as a polynomial in the challenge.
* `ReedSolomon.frobeniusPowerCoordinate`: a coordinate vector with challenge exponents scaled
  by a natural number.
* `ReedSolomon.curveDiscrepancy`: the discrepancy at one coordinate as a polynomial in the
  challenge.
* `ReedSolomon.HasExactPowerAgreement`: exact power agreement, with the challenge and the
  candidate polynomial in an extension field `E` given by `φ : F →+* E`.
* `ReedSolomon.UniformExactPowerAgreement`: one exceptional set of at most `e` challenges for
  every candidate with at least `L` agreements.

## Main statements

* `ReedSolomon.frobeniusPowerCoordinate_eval` and
  `ReedSolomon.frobeniusPowerCoordinate_natDegree_le`: evaluation and degree bounds for sparse
  coordinates.
* `ReedSolomon.exists_exceptional_powerBatched_agreement` and
  `ReedSolomon.exists_exceptional_powerBatched_family`: outside at most `ℓ * (|ι| - L)`
  challenges per tuple, the agreement set of the batched polynomial is the common agreement set.
* `ReedSolomon.mem_polynomialTupleFamily_iff` and
  `ReedSolomon.mem_polynomialTupleFamily_of_commonAgreement`:
  the degree and common-agreement characterization of the interpolant family.
* `ReedSolomon.polynomialTupleFamily_card_le`: the sample-size bound for the interpolant family.
* `ReedSolomon.exists_polynomialGraph_of_sample`: a sample of `k` coordinates determines every
  batched polynomial of degree below `k` that agrees with the batched word on it, over every
  extension field.
* `ReedSolomon.HasExactPowerAgreement.descend` and
  `ReedSolomon.uniformExactPowerAgreement_of_extension`: exact power agreement descends from an
  extension field.
* `ReedSolomon.uniformExactPowerAgreement_of_all_samples`: retaining all common-sample
  interpolants gives a characteristic-free uniform recovery bound.
* `ReedSolomon.determinedByAgreement_code`: Reed–Solomon codewords of message length `k` are
  determined by `a ≥ k` agreements.
* `ReedSolomon.exists_powerBatchedPolynomial_eq`: a codeword decomposition of a polynomial's
  evaluations lifts to a polynomial decomposition.
* `ReedSolomon.uniformExactPowerAgreement_singleton`: a single received word has uniform exact
  power agreement with no exceptional challenge.
* `ReedSolomon.exists_exactPower_fullDimension` and
  `ReedSolomon.uniformExactPowerAgreement_fullDimension`: every full-agreement candidate has exact
  power agreement at full message dimension, with no exceptional challenge.
* `ReedSolomon.hasExactPowerAgreement_id_iff_hasExactAgreement` and
  `ReedSolomon.uniformExactPowerAgreement_iff_uniformExactAgreement`: the polynomial predicates
  are the code-level predicates for `univariatePowersGenerator`.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions

noncomputable section

section Batching

variable {F ι : Type*} [Field F] {ℓ : ℕ}

/-- The received word obtained by batching the words `w t` with the powers `z ^ t` of one
challenge: `i ↦ ∑ t, z ^ t * w t i`. -/
def powerBatchedWord (w : Fin (ℓ + 1) → ι → F) (z : F) : ι → F :=
  fun i ↦ ∑ t, z ^ t.val * w t i

/-- The combination `∑ t, z ^ t • P t` of message polynomials. -/
def powerBatchedPolynomial (P : Fin (ℓ + 1) → F[X]) (z : F) : F[X] :=
  ∑ t, z ^ t.val • P t

/-- Batching preserves the degree bound `degree < k`, including for `k = 0`. -/
theorem powerBatchedPolynomial_degree_lt (P : Fin (ℓ + 1) → F[X]) (z : F) (k : ℕ)
    (hP : ∀ t, (P t).degree < k) : (powerBatchedPolynomial P z).degree < k := by
  rw [← mem_degreeLT]
  exact Submodule.sum_mem _ fun t _ ↦ Submodule.smul_mem _ _ (mem_degreeLT.mpr (hP t))

/-- Evaluation commutes with batching. -/
theorem powerBatchedPolynomial_eval (P : Fin (ℓ + 1) → F[X]) (z x : F) :
    (powerBatchedPolynomial P z).eval x = ∑ t, z ^ t.val * (P t).eval x := by
  simp [powerBatchedPolynomial, eval_finsetSum]

/-- The coordinates where every polynomial `P t` agrees with its received word `w t`. -/
def commonCurveAgreementSet [DecidableEq F] [Fintype ι] (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) (P : Fin (ℓ + 1) → F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ ∀ t, (P t).eval (domain i) = w t i

/-- Coordinate `i` is in `commonCurveAgreementSet domain w P` exactly when every `P t` evaluates
to `w t i` at `domain i`. -/
@[simp] theorem mem_commonCurveAgreementSet [DecidableEq F] [Fintype ι] (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) (P : Fin (ℓ + 1) → F[X]) (i : ι) :
    i ∈ commonCurveAgreementSet domain w P ↔ ∀ t, (P t).eval (domain i) = w t i := by
  simp [commonCurveAgreementSet]

/-- The batched word is the combination of the words `w t` under
`univariatePowersGenerator F ℓ`. -/
theorem powerBatchedWord_eq_sum {F : Type} [Field F] (w : Fin (ℓ + 1) → ι → F) (z : F) :
    powerBatchedWord w z = fun i ↦ ∑ t, univariatePowersGenerator F ℓ z t • w t i := rfl

end Batching

section Coordinate

variable {R : Type*} [CommSemiring R] {ℓ : ℕ}

/-- The polynomial `∑ t, w t * X ^ t` in the batching challenge. Its value at `z` is the batched
coordinate `∑ t, z ^ t * w t`. -/
def powerBatchedCoordinate (w : Fin (ℓ + 1) → R) : R[X] :=
  ∑ t, monomial t.val (w t)

/-- The value of `powerBatchedCoordinate w` at `z` is `∑ t, z ^ t * w t`. -/
theorem powerBatchedCoordinate_eval (w : Fin (ℓ + 1) → R) (z : R) :
    (powerBatchedCoordinate w).eval z = ∑ t, z ^ t.val * w t := by
  simp [powerBatchedCoordinate, eval_finsetSum, mul_comm]

/-- `powerBatchedCoordinate w` has degree at most `ℓ`. -/
theorem powerBatchedCoordinate_natDegree_le (w : Fin (ℓ + 1) → R) :
    (powerBatchedCoordinate w).natDegree ≤ ℓ :=
  natDegree_sum_le_of_forall_le _ _ fun t _ ↦
    (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp t.isLt)

/-- `powerBatchedCoordinate w` is Mathlib's `ofFn (ℓ + 1) w`. -/
theorem powerBatchedCoordinate_eq_ofFn [DecidableEq R] (w : Fin (ℓ + 1) → R) :
    powerBatchedCoordinate w = ofFn (ℓ + 1) w :=
  (ofFn_eq_sum_monomial w).symm

/-- The coefficient of `X ^ t` in `powerBatchedCoordinate w` is `w t`. -/
@[simp] theorem powerBatchedCoordinate_coeff (w : Fin (ℓ + 1) → R) (t : Fin (ℓ + 1)) :
    (powerBatchedCoordinate w).coeff t = w t := by
  classical
  rw [powerBatchedCoordinate_eq_ofFn, ofFn_coeff_eq_val_of_lt w t.isLt]

/-- The polynomial coordinate whose challenge exponents are scaled by `s`. -/
def frobeniusPowerCoordinate (s : ℕ) (values : Fin (ℓ + 1) → R) : R[X] :=
  Polynomial.expand R s (powerBatchedCoordinate values)

/-- Evaluation of `frobeniusPowerCoordinate` scales each challenge exponent by `s`. -/
theorem frobeniusPowerCoordinate_eval (s : ℕ) (values : Fin (ℓ + 1) → R) (z : R) :
    (frobeniusPowerCoordinate s values).eval z =
      ∑ t, z ^ (s * t.val) * values t := by
  rw [frobeniusPowerCoordinate, Polynomial.expand_eval, powerBatchedCoordinate_eval]
  apply Finset.sum_congr rfl
  intro t _
  rw [pow_mul]

/-- The degree of `frobeniusPowerCoordinate` is at most `s * ℓ`. -/
theorem frobeniusPowerCoordinate_natDegree_le (s : ℕ) (values : Fin (ℓ + 1) → R) :
    (frobeniusPowerCoordinate s values).natDegree ≤ s * ℓ := by
  rw [frobeniusPowerCoordinate, Polynomial.natDegree_expand]
  exact (Nat.mul_le_mul_right s (powerBatchedCoordinate_natDegree_le values)).trans_eq
    (Nat.mul_comm _ _)

/-- A coordinate vector is determined by its polynomial `powerBatchedCoordinate`. -/
theorem powerBatchedCoordinate_injective :
    Function.Injective (powerBatchedCoordinate (R := R) (ℓ := ℓ)) := by
  classical
  rw [show powerBatchedCoordinate (R := R) (ℓ := ℓ) = ofFn (ℓ + 1) from
    _root_.funext powerBatchedCoordinate_eq_ofFn]
  exact injective_ofFn _

/-- `powerBatchedCoordinate w` is zero exactly when `w` is. -/
@[simp] theorem powerBatchedCoordinate_eq_zero_iff (w : Fin (ℓ + 1) → R) :
    powerBatchedCoordinate w = 0 ↔ w = 0 := by
  rw [← powerBatchedCoordinate_injective.eq_iff]
  simp [powerBatchedCoordinate]

end Coordinate

section Discrepancy

variable {F ι : Type*} [Field F] {ℓ : ℕ}

/-- The discrepancy at coordinate `i` as a polynomial in the batching challenge: the coefficient of
`X ^ t` is `(P t).eval (domain i) - w t i`. -/
def curveDiscrepancy (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (P : Fin (ℓ + 1) → F[X])
    (i : ι) : F[X] :=
  powerBatchedCoordinate fun t ↦ (P t).eval (domain i) - w t i

/-- `curveDiscrepancy domain w P i` has degree at most `ℓ`. -/
theorem curveDiscrepancy_natDegree_le (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (i : ι) : (curveDiscrepancy domain w P i).natDegree ≤ ℓ :=
  powerBatchedCoordinate_natDegree_le _

/-- At the challenge `z`, the discrepancy is the batched polynomial's value minus the batched
word at coordinate `i`. -/
theorem curveDiscrepancy_eval (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (i : ι) (z : F) :
    (curveDiscrepancy domain w P i).eval z =
      (powerBatchedPolynomial P z).eval (domain i) - powerBatchedWord w z i := by
  simp [curveDiscrepancy, powerBatchedCoordinate_eval, powerBatchedPolynomial_eval,
    powerBatchedWord, mul_sub, Finset.sum_sub_distrib]

/-- The discrepancy at `i` is the zero polynomial exactly when every `P t` agrees with `w t`
at `i`. -/
theorem curveDiscrepancy_eq_zero_iff (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (i : ι) :
    curveDiscrepancy domain w P i = 0 ↔ ∀ t, (P t).eval (domain i) = w t i := by
  simp [curveDiscrepancy, funext_iff, sub_eq_zero]

variable [DecidableEq F] [Fintype ι]

/-- **Few challenges create extra agreement.** If the `P t` agree with the `w t` simultaneously on
at least `L` coordinates, then outside a set of at most `ℓ * (|ι| - L)` challenges `z`, the
agreement set of `∑ t, z ^ t • P t` with the batched word is exactly the common agreement set
of the `P t`.

Each coordinate outside the common agreement set contributes the at most `ℓ` roots of its
discrepancy polynomial. No assumption on the characteristic is needed. -/
theorem exists_exceptional_powerBatched_agreement (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (L : ℕ) (hcommon : L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset F, exceptional.card ≤ ℓ * (Fintype.card ι - L) ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet domain (powerBatchedWord w z) (powerBatchedPolynomial P z) =
          commonCurveAgreementSet domain w P := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ := exists_card_le_forall_eval_eq_zero_iff
    (curveDiscrepancy domain w P) (Finset.univ \ commonCurveAgreementSet domain w P)
    (fun i _ ↦ curveDiscrepancy_natDegree_le domain w P i)
    (fun i hi ↦ (curveDiscrepancy_eq_zero_iff domain w P i).mpr (by simpa using hi))
  refine ⟨exceptional, hcard.trans (Nat.mul_le_mul_left _ ?_), fun z hz ↦ ?_⟩
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  · ext i
    have := hgood z hz i
    rw [curveDiscrepancy_eval, sub_eq_zero, curveDiscrepancy_eq_zero_iff] at this
    simpa using this

/-- A finite family of tuples, each with at least `L` common agreements, has one set of at most
`family.card * (ℓ * (|ι| - L))` challenges outside which no member gains extra agreement. -/
theorem exists_exceptional_powerBatched_family (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (family : Finset (Fin (ℓ + 1) → F[X])) (L : ℕ)
    (hcommon : ∀ P ∈ family, L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset F, exceptional.card ≤ family.card * (ℓ * (Fintype.card ι - L)) ∧
      ∀ P ∈ family, ∀ z ∉ exceptional,
        polynomialAgreementSet domain (powerBatchedWord w z) (powerBatchedPolynomial P z) =
          commonCurveAgreementSet domain w P := by
  classical
  choose! ex hcard hgood using fun P hP ↦
    exists_exceptional_powerBatched_agreement domain w P L (hcommon P hP)
  refine ⟨family.biUnion ex, Finset.card_biUnion_le_card_mul _ _ _ hcard,
    fun P hP z hz ↦ hgood P hP z fun hmem ↦ hz (Finset.mem_biUnion.mpr ⟨P, hP, hmem⟩)⟩

end Discrepancy

section Interpolation

variable {F ι : Type*} [Field F] {ℓ : ℕ}

/-- The finite family of tuples interpolated from received values on a common sample. -/
def polynomialTupleFamily [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (k : ℕ) :
    Finset (Fin (ℓ + 1) → F[X]) := by
  classical
  exact (Finset.univ.powersetCard k).image fun sample t ↦
    Lagrange.interpolate sample domain (w t)

/-- A degree-bounded tuple with at least `k` common agreements belongs to the interpolation
family. -/
theorem mem_polynomialTupleFamily_of_commonAgreement [Fintype ι] [DecidableEq ι]
    [DecidableEq F] (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (k : ℕ)
    (hdegree : ∀ t, (P t).degree < k)
    (hcommon : k ≤ (commonCurveAgreementSet domain w P).card) :
    P ∈ polynomialTupleFamily domain w k := by
  classical
  obtain ⟨sample, hsub, hcard⟩ := Finset.exists_subset_card_eq hcommon
  have hinj : Set.InjOn domain sample := domain.injective.injOn
  apply Finset.mem_image.mpr
  refine ⟨sample, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
  funext t
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample hinj
  · exact Lagrange.degree_interpolate_lt (w t) hinj
  · simpa only [hcard] using hdegree t
  · intro i hi
    rw [Lagrange.eval_interpolate_at_node (w t) hinj hi]
    have himem := hsub hi
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at himem
    exact (himem t).symm

/-- The interpolation family has at most one tuple for each `k`-element sample. -/
theorem polynomialTupleFamily_card_le [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (k : ℕ) :
    (polynomialTupleFamily domain w k).card ≤ (Fintype.card ι).choose k := by
  classical
  exact Finset.card_image_le.trans_eq (by simp)

/-- The interpolation family consists exactly of degree-bounded tuples with at least `k` common
agreements. -/
theorem mem_polynomialTupleFamily_iff [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (k : ℕ) :
    P ∈ polynomialTupleFamily domain w k ↔
      (∀ t, (P t).degree < k) ∧ k ≤ (commonCurveAgreementSet domain w P).card := by
  classical
  constructor
  · intro hP
    obtain ⟨sample, hsample, rfl⟩ := Finset.mem_image.mp hP
    have hcard := (Finset.mem_powersetCard.mp hsample).2
    have hinj : Set.InjOn domain sample := domain.injective.injOn
    constructor
    · intro t
      simpa only [hcard] using Lagrange.degree_interpolate_lt (w t) hinj
    · rw [← hcard]
      apply Finset.card_le_card
      intro i hi
      simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro t
      exact Lagrange.eval_interpolate_at_node (w t) hinj hi
  · rintro ⟨hdegree, hcommon⟩
    exact mem_polynomialTupleFamily_of_commonAgreement domain w P k hdegree hcommon

/-- Interpolating each word `w t` on a finite sample set gives polynomials `P t` of degree below
any `k ≥ samples.card` that agree with every `w t` on the samples. -/
theorem exists_polynomialTuple_interpolating (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    {k : ℕ} (samples : Finset ι) (hcard : samples.card ≤ k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      ∀ i ∈ samples, ∀ t, (P t).eval (domain i) = w t i := by
  classical
  refine ⟨fun t ↦ Lagrange.interpolate samples domain (w t), fun t ↦ ?_, fun i hi t ↦ ?_⟩
  · exact (Lagrange.degree_interpolate_lt _ domain.injective.injOn).trans_le
      (by exact_mod_cast hcard)
  · exact Lagrange.eval_interpolate_at_node (w t) domain.injective.injOn hi

/-- Two tuples of polynomials of degree below `k ≤ samples.card` that agree with the same words on
the samples are equal. -/
theorem polynomialTuple_eq_of_common_samples (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P Q : Fin (ℓ + 1) → F[X]) {k : ℕ} (samples : Finset ι) (hcard : k ≤ samples.card)
    (hP : ∀ t, (P t).degree < k) (hQ : ∀ t, (Q t).degree < k)
    (hPs : ∀ i ∈ samples, ∀ t, (P t).eval (domain i) = w t i)
    (hQs : ∀ i ∈ samples, ∀ t, (Q t).eval (domain i) = w t i) : P = Q := by
  have hk : (k : WithBot ℕ) ≤ samples.card := by exact_mod_cast hcard
  funext t
  exact eq_of_degrees_lt_of_eval_index_eq samples domain.injective.injOn
    ((hP t).trans_le hk) ((hQ t).trans_le hk) fun i hi ↦ (hPs i hi t).trans (hQs i hi t).symm

/-- **A sample of `k` coordinates determines the batched polynomial.** For a sample set of size
`k`, the interpolating tuple `P` of degree below `k` has the property that over every field `E`
with `φ : F →+* E`, each polynomial `Q` of degree below `k` agreeing with the batched word at
`z : E` on the samples equals `∑ t, z ^ t • (P t).map φ`. -/
theorem exists_polynomialGraph_of_sample (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) {k : ℕ}
    (samples : Finset ι) (hcard : samples.card = k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ samples, ∀ t, (P t).eval (domain i) = w t i) ∧
      ∀ {E : Type*} [Field E] (φ : F →+* E) (z : E) (Q : E[X]), Q.degree < k →
        (∀ i ∈ samples, Q.eval (φ (domain i)) = ∑ t, z ^ t.val * φ (w t i)) →
        Q = powerBatchedPolynomial (fun t ↦ (P t).map φ) z := by
  obtain ⟨P, hP, hs⟩ := exists_polynomialTuple_interpolating domain w samples hcard.le
  refine ⟨P, hP, hs, fun φ z Q hQ hQs ↦ ?_⟩
  subst hcard
  refine eq_of_degrees_lt_of_eval_index_eq samples
    (fun _ _ _ _ h ↦ domain.injective (φ.injective h)) hQ
    (powerBatchedPolynomial_degree_lt _ z _ fun t ↦ degree_map_le.trans_lt (hP t))
    fun i hi ↦ ?_
  rw [powerBatchedPolynomial_eval, hQs i hi]
  simp [eval_map, eval₂_at_apply, hs i hi]

end Interpolation

section ScalarExtension

variable {F E ι : Type*} [Field F] [Field E] {ℓ : ℕ}

/-- Applying `φ : F →+* E` to the words and the challenge batches to `φ` of the batched word. -/
theorem powerBatchedWord_map (w : Fin (ℓ + 1) → ι → F) (φ : F →+* E) (z : F) :
    powerBatchedWord (fun t i ↦ φ (w t i)) (φ z) = fun i ↦ φ (powerBatchedWord w z i) := by
  funext i
  simp [powerBatchedWord]

/-- Mapping the batched polynomial along `φ : F →+* E` batches the mapped polynomials at `φ z`. -/
theorem powerBatchedPolynomial_map (P : Fin (ℓ + 1) → F[X]) (φ : F →+* E) (z : F) :
    (powerBatchedPolynomial P z).map φ =
      powerBatchedPolynomial (fun t ↦ (P t).map φ) (φ z) := by
  simp [powerBatchedPolynomial, smul_eq_C_mul, Polynomial.map_sum]

end ScalarExtension

section Exact

variable {F E ι : Type*} [Field F] [Field E] [Fintype ι] [DecidableEq F] [DecidableEq E] {ℓ : ℕ}

/-- **Exact power agreement.** The polynomial `Q` over `E` is `∑ t, z ^ t • (P t).map φ` for
message polynomials `P t` over `F` of degree below `k`, and the coordinates where `Q` agrees with
the batched received word are exactly those where every `P t` agrees with `w t`.

The equality of agreement sets is the substance: it says that `Q` has no agreement beyond the
common agreement of the constituents. The embedding `φ` allows the challenge and `Q` to live in an
extension field while the messages and received words stay over `F`; the Reed–Solomon statements
in this file use `φ = RingHom.id F`. -/
def HasExactPowerAgreement (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (φ : F →+* E) (k : ℕ)
    (z : E) (Q : E[X]) : Prop :=
  ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
    Q = powerBatchedPolynomial (fun t ↦ (P t).map φ) z ∧
    polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
        (powerBatchedWord (fun t i ↦ φ (w t i)) z) Q =
      commonCurveAgreementSet domain w P

/-- **Uniform exact power agreement.** One set `bad` of at most `e` challenges, chosen after the
received words `w`, such that every challenge `z ∉ bad` and every polynomial `Q` of degree below
`k` with at least `L` agreements with the batched word has exact power agreement.

The bad set does not depend on `Q`; this quantifier order is what the interleaved transfer
needs. -/
def UniformExactPowerAgreement (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (k L e : ℕ) : Prop :=
  ∃ bad : Finset F, bad.card ≤ e ∧ ∀ z ∉ bad, ∀ Q : F[X], Q.degree < k →
    L ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
    HasExactPowerAgreement domain w (RingHom.id F) k z Q

/-- With `φ = RingHom.id F`, exact power agreement is stated over `F` directly: `Q` is
`∑ t, z ^ t • P t` and its agreement set with `powerBatchedWord w z` is the common agreement set
of the `P t`. -/
theorem hasExactPowerAgreement_id_iff (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (k : ℕ) (z : F)
    (Q : F[X]) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q ↔
      ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧ Q = powerBatchedPolynomial P z ∧
        polynomialAgreementSet domain (powerBatchedWord w z) Q =
          commonCurveAgreementSet domain w P := by
  have hdomain : domain.trans ⟨RingHom.id F, (RingHom.id F).injective⟩ = domain :=
    Function.Embedding.ext fun _ ↦ rfl
  simp only [HasExactPowerAgreement, Polynomial.map_id, RingHom.id_apply, hdomain]

/-- A single received word has uniform exact power agreement with no exceptional challenge, for
every degree bound `k` and agreement threshold `L`: the witness is `P 0 = Q`. -/
theorem uniformExactPowerAgreement_singleton (domain : ι ↪ F) (w : Fin 1 → ι → F) (k L : ℕ) :
    UniformExactPowerAgreement domain w k L 0 := by
  refine ⟨∅, by simp, fun z _ Q hQ _ ↦ ?_⟩
  refine (hasExactPowerAgreement_id_iff _ _ _ _ _).mpr ⟨fun _ ↦ Q, fun _ ↦ hQ, ?_, ?_⟩
  · simp [powerBatchedPolynomial]
  · ext i
    simp [powerBatchedWord]

/-- At full message dimension, one tuple of interpolants explains every candidate that agrees
with the batched word on all coordinates, and its agreement set is the tuple's common agreement
set. -/
theorem exists_exactPower_fullDimension (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < Fintype.card ι) ∧
      ∀ z (Q : F[X]), Q.degree < Fintype.card ι →
        Fintype.card ι ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
        HasExactPowerAgreement domain w (RingHom.id F) (Fintype.card ι) z Q := by
  classical
  obtain ⟨P, hP, hsample, hrecognize⟩ :=
    exists_polynomialGraph_of_sample (k := Fintype.card ι) domain w Finset.univ (by simp)
  refine ⟨P, hP, ?_⟩
  intro z Q hQ hcard
  have hfull : polynomialAgreementSet domain (powerBatchedWord w z) Q = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hupper : (polynomialAgreementSet domain (powerBatchedWord w z) Q).card ≤
        Fintype.card ι := by
      simpa using (polynomialAgreementSet domain (powerBatchedWord w z) Q).card_le_univ
    exact Nat.le_antisymm hupper hcard
  have heval : ∀ i ∈ (Finset.univ : Finset ι),
      Q.eval (domain i) = ∑ t, z ^ t.val * w t i := by
    intro i hi
    have hmem : i ∈ polynomialAgreementSet domain (powerBatchedWord w z) Q := by
      rw [hfull]
      exact hi
    simpa only [powerBatchedWord] using (Finset.mem_filter.mp hmem).2
  refine (hasExactPowerAgreement_id_iff domain w _ z Q).mpr ?_
  refine ⟨P, hP, ?_, ?_⟩
  · simpa only [Polynomial.map_id, RingHom.id_apply] using
      hrecognize (RingHom.id F) z Q hQ (fun i _ ↦ heval i (Finset.mem_univ i))
  · have hfullMapped :
        polynomialAgreementSet domain (powerBatchedWord w z) Q = Finset.univ := hfull
    rw [hfullMapped]
    symm
    apply Finset.eq_univ_of_forall
    intro i
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hsample i (Finset.mem_univ i)

/-- At full message dimension, uniform exact power agreement holds with no exceptional
challenges. -/
theorem uniformExactPowerAgreement_fullDimension (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) :
    UniformExactPowerAgreement domain w (Fintype.card ι) (Fintype.card ι) 0 := by
  obtain ⟨P, hP, hgood⟩ := exists_exactPower_fullDimension domain w
  refine ⟨∅, by simp, ?_⟩
  intro z _ Q hQ hcard
  exact hgood z Q hQ hcard

end Exact

section Descent

variable {F E ι : Type*} [Field F] [Field E] [Fintype ι] [DecidableEq F] [DecidableEq E] {ℓ : ℕ}

/-- Exact power agreement over an extension descends: if `Q.map φ` has exact power agreement at
the challenge `φ z`, then `Q` has exact power agreement at `z` over `F`. The same tuple `P` is a
witness. -/
theorem HasExactPowerAgreement.descend {domain : ι ↪ F} {w : Fin (ℓ + 1) → ι → F}
    {φ : F →+* E} {k : ℕ} {z : F} {Q : F[X]}
    (h : HasExactPowerAgreement domain w φ k (φ z) (Q.map φ)) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q := by
  obtain ⟨P, hP, heq, hagree⟩ := h
  refine (hasExactPowerAgreement_id_iff domain w k z Q).mpr ⟨P, hP, ?_, ?_⟩
  · exact map_injective φ φ.injective (heq.trans (powerBatchedPolynomial_map P φ z).symm)
  · rwa [powerBatchedWord_map, polynomialAgreementSet_map] at hagree

/-- **Descent of uniform exact power agreement.** Suppose a set `exceptional` of challenges in
an extension `E` is such that at every other challenge, every polynomial `Q` over `E` of degree
below `k` with at least `L` agreements with the batched word has exact power agreement. Then
uniform exact power agreement holds over `F` with at most `exceptional.card` exceptional
challenges: the preimage of `exceptional` under `φ`. -/
theorem uniformExactPowerAgreement_of_extension (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (φ : F →+* E) (k L : ℕ) (exceptional : Finset E)
    (hgood : ∀ z ∉ exceptional, ∀ Q : E[X], Q.degree < k →
      L ≤ (polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
        (powerBatchedWord (fun t i ↦ φ (w t i)) z) Q).card →
      HasExactPowerAgreement domain w φ k z Q) :
    UniformExactPowerAgreement domain w k L exceptional.card := by
  refine ⟨exceptional.preimage φ φ.injective.injOn,
    Finset.card_le_card_of_injOn φ (fun z hz ↦ Finset.mem_preimage.mp hz) φ.injective.injOn,
    fun z hz Q hQ hL ↦ ?_⟩
  refine (hgood (φ z) (fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)) (Q.map φ)
    (degree_map_le.trans_lt hQ) ?_).descend
  rwa [powerBatchedWord_map, polynomialAgreementSet_map]

end Descent

section AllSamples

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F] {ℓ k L : ℕ}

/-- Retaining every common-sample interpolant gives uniform exact recovery over any field. One
exceptional set works for every challenge outside it and every close polynomial, with at most
`(|ι| choose k) * (ℓ * (|ι| - k))` exceptional challenges. -/
theorem uniformExactPowerAgreement_of_all_samples (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) (hkL : k ≤ L) :
    UniformExactPowerAgreement domain w k L
      ((Fintype.card ι).choose k * (ℓ * (Fintype.card ι - k))) := by
  classical
  let family := polynomialTupleFamily domain w k
  have hdegree : ∀ P ∈ family, ∀ t, (P t).degree < k := by
    intro P hP
    exact ((mem_polynomialTupleFamily_iff domain w P k).mp hP).1
  have hcommon : ∀ P ∈ family, k ≤ (commonCurveAgreementSet domain w P).card := by
    intro P hP
    exact ((mem_polynomialTupleFamily_iff domain w P k).mp hP).2
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_powerBatched_family domain w family k hcommon
  refine ⟨exceptional, ?_, ?_⟩
  · exact hcard.trans
      (Nat.mul_le_mul_right _ (polynomialTupleFamily_card_le domain w k))
  · intro z hz Q hQdegree hAgreement
    have hkAgreement : k ≤
        (polynomialAgreementSet domain (powerBatchedWord w z) Q).card :=
      hkL.trans hAgreement
    obtain ⟨sample, hsampleSubset, hsampleCard⟩ :=
      Finset.exists_subset_card_eq hkAgreement
    obtain ⟨P, hPdegree, hPsample, hPidentity⟩ :=
      exists_polynomialGraph_of_sample domain w sample hsampleCard
    have hPcommon : k ≤ (commonCurveAgreementSet domain w P).card := by
      rw [← hsampleCard]
      apply Finset.card_le_card
      intro i hi
      simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hPsample i hi
    have hPmem : P ∈ family := by
      exact (mem_polynomialTupleFamily_iff domain w P k).mpr ⟨hPdegree, hPcommon⟩
    have hQsample : ∀ i ∈ sample,
        Q.eval (domain i) = ∑ t, z ^ t.val * w t i := by
      intro i hi
      exact (Finset.mem_filter.mp (hsampleSubset hi)).2
    have hQidentity : Q = powerBatchedPolynomial P z := by
      simpa only [Polynomial.map_id] using
        hPidentity (RingHom.id F) z Q hQdegree hQsample
    refine (hasExactPowerAgreement_id_iff domain w k z Q).mpr
      ⟨P, hPdegree, hQidentity, ?_⟩
    rw [hQidentity]
    exact hgood P hPmem z hz

end AllSamples

section CodeLevel

variable {F : Type} {ι : Type*} [Field F] {ℓ : ℕ}

/-- **Reed–Solomon codewords are determined by `k` agreements.** Two codewords of the code of
message length `k` that agree on at least `a ≥ k` coordinates are equal, since the difference of
their message polynomials has degree below `k` and at least `k` roots among distinct evaluation
points. The hypothesis `k ≤ a` is needed: for `a < k ≤ |ι|`, the code contains a nonzero codeword
vanishing on `a` chosen coordinates. -/
theorem determinedByAgreement_code (domain : ι ↪ F) {k a : ℕ} (hk : k ≤ a) :
    Code.DeterminedByAgreement (code domain k) a := by
  intro c hc c' hc' T hT hcT
  obtain ⟨p, hp, hpc⟩ := mem_code_iff_eval.mp hc
  obtain ⟨p', hp', hpc'⟩ := mem_code_iff_eval.mp hc'
  have hkT : ((k : ℕ) : WithBot ℕ) ≤ (T.card : WithBot ℕ) := by exact_mod_cast hk.trans hT
  have hpp : p = p' := Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := T)
    domain.injective.injOn (hp.trans_le hkT) (hp'.trans_le hkT) fun i hi ↦ by
      rw [hpc, hpc', hcT i hi]
  funext i
  rw [← hpc, ← hpc', hpp]

/-- **Polynomial decomposition from a codeword decomposition.** Let `Q` have degree below `k` and
let its evaluations be `∑ t, z ^ t * c' t i` for codewords `c' t` of the Reed–Solomon code of
message length `k`. Then there are polynomials `P t` of degree below `k` evaluating to `c' t`
with `Q = ∑ t, z ^ t • P t`.

When `k ≤ |ι|` the evaluations determine the polynomials and any choice of `P t` works. When
`k > |ι|` they do not, and the difference `Q - ∑ t, z ^ t • P t`, which vanishes on the domain,
is added to `P 0`; this uses that the weight of `P 0` is `z ^ 0 = 1`. So no relation between `k`
and `|ι|` is needed. -/
theorem exists_powerBatchedPolynomial_eq (domain : ι ↪ F) {k : ℕ} {z : F} {Q : F[X]}
    (hQ : Q.degree < k) {c' : Fin (ℓ + 1) → ι → F} (hc' : ∀ t, c' t ∈ code domain k)
    (hsum : ∀ i, Q.eval (domain i) = ∑ t, z ^ t.val * c' t i) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ t i, (P t).eval (domain i) = c' t i) ∧ Q = powerBatchedPolynomial P z := by
  choose P₀ hP₀ hP₀c using fun t ↦ mem_code_iff_eval.mp (hc' t)
  set D := Q - powerBatchedPolynomial P₀ z with hD
  have hDdeg : D ∈ degreeLT F k := Submodule.sub_mem _ (mem_degreeLT.mpr hQ)
    (mem_degreeLT.mpr (powerBatchedPolynomial_degree_lt P₀ z k hP₀))
  have hDeval (i : ι) : D.eval (domain i) = 0 := by
    rw [hD, eval_sub, powerBatchedPolynomial_eval, hsum]
    simp [hP₀c]
  refine ⟨fun t ↦ P₀ t + if t = 0 then D else 0, fun t ↦ ?_, fun t i ↦ ?_, ?_⟩
  · rw [← mem_degreeLT]
    refine Submodule.add_mem _ (mem_degreeLT.mpr (hP₀ t)) ?_
    split_ifs
    · exact hDdeg
    · exact Submodule.zero_mem _
  · dsimp only
    split_ifs <;> simp [hP₀c, hDeval]
  · simp only [powerBatchedPolynomial, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.val_zero, pow_zero, one_smul]
    change Q = powerBatchedPolynomial P₀ z + D
    rw [hD]
    ring

variable [Fintype ι] [DecidableEq F]

/-- **Exact power agreement is exact agreement for the code.** For a polynomial `Q` of degree
below `k`, exact power agreement at `z` (with `φ = RingHom.id F`) is `Code.HasExactAgreement`
for the Reed–Solomon code, the batching map `univariatePowersGenerator F ℓ`, and the codeword
of evaluations of `Q`.

From left to right, the witnesses are the evaluations of the `P t`. From right to left, the
codeword witnesses are lifted by `exists_powerBatchedPolynomial_eq`, which needs no bound
relating `k` and `|ι|`. -/
theorem hasExactPowerAgreement_id_iff_hasExactAgreement (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) {k : ℕ} {z : F} {Q : F[X]} (hQ : Q.degree < k) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q ↔
      Code.HasExactAgreement (univariatePowersGenerator F ℓ) (code domain k) z w
        (evalOnPoints domain Q) := by
  constructor
  · rintro ⟨P, hP, hQP, hset⟩
    simp only [Polynomial.map_id] at hQP
    refine ⟨fun t ↦ evalOnPoints domain (P t), fun t ↦
      evalOnPoints_mem_code_of_degree_lt (hP t), ?_, fun i ↦ ?_⟩
    · funext i
      simp [evalOnPoints, hQP, powerBatchedPolynomial_eval]
    · have := congrArg (i ∈ ·) hset
      simpa [evalOnPoints, powerBatchedWord] using this
  · rintro ⟨c', hc', hcsum, hiff⟩
    obtain ⟨P, hP, hPc, hQP⟩ := exists_powerBatchedPolynomial_eq domain hQ hc' fun i ↦ by
      simpa [evalOnPoints] using congrFun hcsum i
    refine ⟨P, hP, by simpa using hQP, ?_⟩
    ext i
    have := hiff i
    simp only [evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, univariatePowersGenerator,
      smul_eq_mul] at this
    simp [powerBatchedWord, hPc, this]

/-- **Uniform exact power agreement is uniform exact agreement for the code.** The polynomial
statement `UniformExactPowerAgreement domain w k L e` is `Code.UniformExactAgreement` for the
Reed–Solomon code of message length `k` and the batching map `univariatePowersGenerator F ℓ`,
with the same threshold `L` and count `e`. No relation between `k` and `L` is needed. -/
theorem uniformExactPowerAgreement_iff_uniformExactAgreement (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) {k L e : ℕ} :
    UniformExactPowerAgreement domain w k L e ↔
      Code.UniformExactAgreement (univariatePowersGenerator F ℓ) (code domain k) L e w := by
  constructor
  · rintro ⟨bad, hcard, hbad⟩
    refine ⟨bad, hcard, fun z hz c hc T hT hcT ↦ ?_⟩
    obtain ⟨Q, hQ, hQc⟩ := mem_code_iff_eval.mp hc
    have hc_eq : c = evalOnPoints domain Q := by
      funext i
      simp [evalOnPoints, hQc]
    subst hc_eq
    refine (hasExactPowerAgreement_id_iff_hasExactAgreement domain w hQ).mp
      (hbad z hz Q hQ (hT.trans (Finset.card_le_card fun i hi ↦ ?_)))
    rw [mem_polynomialAgreementSet]
    simpa [evalOnPoints, powerBatchedWord] using hcT i hi
  · rintro ⟨bad, hcard, hbad⟩
    refine ⟨bad, hcard, fun z hz Q hQ hL ↦ ?_⟩
    refine (hasExactPowerAgreement_id_iff_hasExactAgreement domain w hQ).mpr
      (hbad z hz _ (evalOnPoints_mem_code_of_degree_lt hQ) _ hL fun i hi ↦ ?_)
    rw [mem_polynomialAgreementSet] at hi
    simpa [evalOnPoints, powerBatchedWord] using hi

end CodeLevel

end

end ReedSolomon

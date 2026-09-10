/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import ArkLib.ToMathlib.Polynomial.SimultaneousRoots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.Lagrange
/-!
# Agreement on polynomial curves of received words

A single challenge selects the combination with weights `1, z, ..., z^ℓ`.
The discrepancy at each evaluation point is a polynomial in the challenge, distinct
from the message variable. Its coefficients are exactly the constituent discrepancies.
Consequently extra agreements cost at most `ℓ * (n - L)` challenges when the tuple
has at least `L` common agreements. No characteristic bound involving `ℓ` is required.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.6 (Theorem 5.14), polynomial graphs and accidental agreements.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] {n ℓ : ℕ}

/-- The received word obtained by batching with successive powers of one challenge. -/
def powerBatchedWord (w : Fin (ℓ + 1) → Fin n → F) (z : F) : Fin n → F :=
  fun i ↦ ∑ t, z ^ t.val * w t i

/-- The corresponding combination of constituent message polynomials. -/
def powerBatchedPolynomial (P : Fin (ℓ + 1) → F[X]) (z : F) : F[X] :=
  ∑ t, z ^ t.val • P t

/-- A received coordinate as a polynomial in the retained batching challenge. -/
def powerBatchedCoordinate (w : Fin (ℓ + 1) → F) : F[X] :=
  ∑ t, Polynomial.monomial t.val (w t)

theorem powerBatchedCoordinate_eval (w : Fin (ℓ + 1) → F) (z : F) :
    (powerBatchedCoordinate w).eval z = ∑ t, z ^ t.val * w t := by
  change (Polynomial.evalRingHom z) (∑ t, Polynomial.monomial t.val (w t)) = _
  rw [map_sum]
  simp [mul_comm]

theorem powerBatchedCoordinate_natDegree_le (w : Fin (ℓ + 1) → F) :
    (powerBatchedCoordinate w).natDegree ≤ ℓ := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro t _
  exact (Polynomial.natDegree_monomial_le _).trans (Fin.is_le t)

/-- Batching does not increase the message degree. This includes the zero-dimensional code. -/
theorem powerBatchedPolynomial_degree_lt (P : Fin (ℓ + 1) → F[X]) (z : F) (k : ℕ)
    (hP : ∀ t, (P t).degree < k) : (powerBatchedPolynomial P z).degree < k := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  simp only [powerBatchedPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_smul]
  apply Finset.sum_eq_zero
  intro t _
  rw [(Polynomial.degree_lt_iff_coeff_zero (P t) k).mp (hP t) j hj]
  simp

/-- Evaluation commutes with batching the constituent messages. -/
theorem powerBatchedPolynomial_eval (P : Fin (ℓ + 1) → F[X]) (z x : F) :
    (powerBatchedPolynomial P z).eval x = ∑ t, z ^ t.val * (P t).eval x := by
  change (Polynomial.evalRingHom x) (∑ t, z ^ t.val • P t) = _
  rw [map_sum]
  simp [Polynomial.smul_eq_C_mul]

open Classical in
/-- Positions where every constituent polynomial agrees with its received word. -/
def commonCurveAgreementSet (α : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (P : Fin (ℓ + 1) → F[X]) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ ∀ t, (P t).eval (α i) = w t i

/-- The polynomial in the challenge whose coefficients are coordinate discrepancies.
The message variable has already been evaluated at `α i`. -/
def curveDiscrepancy (α : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (P : Fin (ℓ + 1) → F[X]) (i : Fin n) : F[X] :=
  ∑ t, Polynomial.monomial t.val ((P t).eval (α i) - w t i)

theorem curveDiscrepancy_natDegree_le (α : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P : Fin (ℓ + 1) → F[X]) (i : Fin n) :
    (curveDiscrepancy α w P i).natDegree ≤ ℓ := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro t _
  exact (Polynomial.natDegree_monomial_le _).trans (Fin.is_le t)

theorem curveDiscrepancy_eval (α : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P : Fin (ℓ + 1) → F[X]) (i : Fin n) (z : F) :
    (curveDiscrepancy α w P i).eval z =
      (powerBatchedPolynomial P z).eval (α i) - powerBatchedWord w z i := by
  simp [curveDiscrepancy, powerBatchedPolynomial, powerBatchedWord,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.sum_sub_distrib,
    Polynomial.smul_eq_C_mul, mul_comm]

theorem curveDiscrepancy_eq_zero_iff (α : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P : Fin (ℓ + 1) → F[X]) (i : Fin n) :
    curveDiscrepancy α w P i = 0 ↔ ∀ t, (P t).eval (α i) = w t i := by
  classical
  constructor
  · intro h t
    have hc := congrArg (fun Q : F[X] ↦ Q.coeff t.val) h
    simpa [curveDiscrepancy, Polynomial.coeff_monomial, Fin.val_inj,
      sub_eq_zero] using hc
  · intro h
    simp [curveDiscrepancy, h]

open Classical in
/-- A fixed tuple acquires no accidental agreements outside at most `ℓ(n-L)` challenges.
This theorem does not assert that all close candidates arise from such tuples. -/
theorem exists_exceptional_powerBatched_agreement (α : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P : Fin (ℓ + 1) → F[X]) (L : ℕ)
    (hcommon : L ≤ (commonCurveAgreementSet α w P).card) :
    ∃ exceptional : Finset F, exceptional.card ≤ ℓ * (n - L) ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet α (powerBatchedWord w z) (powerBatchedPolynomial P z) =
          commonCurveAgreementSet α w P := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ := Polynomial.exists_exceptional_evaluation_family
    (curveDiscrepancy α w P) (curveDiscrepancy_natDegree_le α w P)
    (L := L) (by simpa [commonCurveAgreementSet, curveDiscrepancy_eq_zero_iff] using hcommon)
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz
  ext i
  simpa [polynomialAgreementSet, commonCurveAgreementSet,
    curveDiscrepancy_eval, sub_eq_zero, curveDiscrepancy_eq_zero_iff] using hgood z hz i

open Classical in
/-- A finite family of tuples shares one exceptional set. Only coordinates outside
the common agreements contribute, for a total cost `family.card * ℓ * (n-L)`. -/
theorem exists_exceptional_powerBatched_family (α : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (family : Finset (Fin (ℓ + 1) → F[X])) (L : ℕ)
    (hcommon : ∀ P ∈ family, L ≤ (commonCurveAgreementSet α w P).card) :
    ∃ exceptional : Finset F, exceptional.card ≤ family.card * (ℓ * (n - L)) ∧
      ∀ P ∈ family, ∀ z ∉ exceptional,
        polynomialAgreementSet α (powerBatchedWord w z) (powerBatchedPolynomial P z) =
          commonCurveAgreementSet α w P := by
  classical
  have h : ∀ P ∈ family, ∃ exceptional : Finset F,
      exceptional.card ≤ ℓ * (n - L) ∧
        ∀ z ∉ exceptional,
          polynomialAgreementSet α (powerBatchedWord w z) (powerBatchedPolynomial P z) =
            commonCurveAgreementSet α w P :=
    fun P hP ↦ exists_exceptional_powerBatched_agreement α w P L (hcommon P hP)
  choose ex hcard hgood using h
  let exceptions (P : Fin (ℓ + 1) → F[X]) :=
    if hP : P ∈ family then ex P hP else ∅
  refine ⟨family.biUnion exceptions, ?_, ?_⟩
  · calc
      (family.biUnion exceptions).card ≤ ∑ P ∈ family, (exceptions P).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _P ∈ family, ℓ * (n - L) := by
        apply Finset.sum_le_sum
        intro P hP
        simpa [exceptions, hP] using hcard P hP
      _ = family.card * (ℓ * (n - L)) := by simp
  · intro P hP z hz
    apply hgood P hP z
    intro hmem
    apply hz
    exact Finset.mem_biUnion.mpr ⟨P, hP, by simpa [exceptions, hP] using hmem⟩

/-- Interpolate each received constituent on the same sample set. This constructs
the polynomial tuple associated with a curve graph cut out by `k` agreement equations. -/
theorem exists_polynomialTuple_interpolating (α : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (k : ℕ) (samples : Finset (Fin n))
    (hcard : samples.card = k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      ∀ i ∈ samples, ∀ t, (P t).eval (α i) = w t i := by
  classical
  refine ⟨fun t ↦ Lagrange.interpolate samples α (w t), ?_, ?_⟩
  · intro t
    simpa [hcard] using Lagrange.degree_interpolate_lt
      (s := samples) (v := α) (r := w t) α.injective.injOn
  · intro i hi t
    exact Lagrange.eval_interpolate_at_node (w t) α.injective.injOn hi

/-- Any `k` common samples uniquely determine a tuple of degree-`< k` polynomials.
The proof works coefficientwise in the batching parameter, in arbitrary characteristic. -/
theorem polynomialTuple_eq_of_common_samples (α : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (P Q : Fin (ℓ + 1) → F[X])
    (k : ℕ) (samples : Finset (Fin n)) (hcard : samples.card = k)
    (hP : ∀ t, (P t).degree < k) (hQ : ∀ t, (Q t).degree < k)
    (hPs : ∀ i ∈ samples, ∀ t, (P t).eval (α i) = w t i)
    (hQs : ∀ i ∈ samples, ∀ t, (Q t).eval (α i) = w t i) : P = Q := by
  funext t
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq samples α.injective.injOn
  · simpa [hcard] using hP t
  · simpa [hcard] using hQ t
  · intro i hi
    exact (hPs i hi t).trans (hQs i hi t).symm

/-- A sample of `k` coordinates recognizes the whole polynomial graph over every extension
field: each message agreeing on that sample is the power combination of the uniquely
interpolated base-field tuple. This is a pointwise statement, with no exceptional challenges. -/
theorem exists_polynomialGraph_of_sample (α : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (k : ℕ) (samples : Finset (Fin n))
    (hcard : samples.card = k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ samples, ∀ t, (P t).eval (α i) = w t i) ∧
      ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E) (Q : E[X]),
        Q.degree < k →
        (∀ i ∈ samples, Q.eval (ι (α i)) = ∑ t, z ^ t.val * ι (w t i)) →
        Q = powerBatchedPolynomial (fun t ↦ (P t).map ι) z := by
  obtain ⟨P, hP, hs⟩ := exists_polynomialTuple_interpolating α w k samples hcard
  refine ⟨P, hP, hs, ?_⟩
  intro E _ ι z Q hQ hQs
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq samples
    (show Set.InjOn (fun i ↦ ι (α i)) (samples : Set (Fin n)) from
      fun _ _ _ _ heq ↦ α.injective (ι.injective heq))
  · simpa [hcard] using hQ
  · rw [hcard]
    exact powerBatchedPolynomial_degree_lt _ z k
      (fun t ↦ Polynomial.degree_map_le.trans_lt (hP t))
  · intro i hi
    rw [powerBatchedPolynomial_eval, hQs i hi]
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hs i hi t]

end
end ReedSolomon

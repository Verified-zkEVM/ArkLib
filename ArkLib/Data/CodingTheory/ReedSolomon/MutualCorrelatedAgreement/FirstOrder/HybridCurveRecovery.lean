/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.OrdinaryTail
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Optimized first-order curve recovery

A nonzero first-order equation, with bounded total jet degree, `Y₁` degree and coefficient
height, has one exceptional set of challenges fixed before every candidate. Outside it, every
low-degree root of the specialized equation that agrees with the power-batched word of a
polynomial curve on at least `A` coordinates has exact power agreement. The bound is
`hybridCurveOptimized`: the ordinary tail and the regular derivative stages choose their
retention thresholds independently, and the maximum over actual derivative degrees is taken last.

Over an arbitrary field the equation is lifted to the algebraic closure and the exceptional set
restricts to the base field. At full message dimension no challenge is exceptional and no
characteristic guard is needed. A strict surplus of shifted height slots constructs the equation,
so optimized curve recovery follows from one numerical inequality.

## Main statements

* `ReedSolomon.exists_exceptional_firstOrder_hybridCurve_optimized`: optimized curve recovery
  over an algebraically closed extension.
* `ReedSolomon.exists_baseExceptional_firstOrder_hybridCurve_optimized`: the same bound with
  the exceptional set and the candidates in an arbitrary base field.
* `ReedSolomon.exists_baseExceptional_firstOrder_hybridCurve_including_fullDimension`: adds the
  full-dimension case, with bound zero and no characteristic guard.
* `ReedSolomon.exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized`: a strict
  shifted-height slot surplus gives optimized curve recovery for every close candidate.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial PolynomialDifferential MvPolynomial

namespace ReedSolomon

open HiddenDerivative

noncomputable section

/-- Let `Q` be a nonzero first-order equation over `E[X]`, with `E` algebraically closed, of
total jet degree at most `mu`, `Y₁` degree at most `M` and coefficient height at most `h`. For
`0 < D, ell`, `D < A ≤ n` and characteristic `0` or above `max D (jetDegree Q 1)`, one
exceptional set of size at most `hybridCurveOptimized n D ell A h mu M` is fixed before every
challenge and candidate. Outside it, every degree-`< D + 1` root of the specialized equation
with at least `A` agreements with the power-batched word has exact power agreement. -/
theorem exists_exceptional_firstOrder_hybridCurve_optimized
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {n D A h mu M ell : ℕ} (domain : Fin n ↪ F)
    (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0) (hweight : jetTotalDegree Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M) (hheight : CoeffNatDegreeLE Q h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D (jetDegree Q (1 : Fin 2)) < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ hybridCurveOptimized n D ell A h mu M ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (domain.trans ⟨iota, iota.injective⟩)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hcharE : ringChar E = 0 ∨ jetDegree Q (1 : Fin 2) < ringChar E := by
    have heq : ringChar E = ringChar F := by
      let _ : CharP E (ringChar F) := charP_of_injective_ringHom iota.injective (ringChar F)
      exact ringChar.eq E (ringChar F)
    rw [heq]
    exact hchar.imp_right fun hc ↦ (le_max_right D _).trans_lt hc
  obtain ⟨descent⟩ := exists_firstOrderHybridDescent Q hQ hweight hdegree hcharE
  exact exists_exceptional_firstOrder_hybridCurve_optimized_of_tail domain values iota Q
    descent hheight hell hD hDA hAn (hchar.imp_right fun hc ↦ (le_max_left D _).trans_lt hc)
    fun _ hDL hLA ↦
      descent.exists_exceptional_ordinaryCurveTail domain values iota hheight hell hD hDL hLA

/-- Over an arbitrary field `F`, let `Q` be a nonzero first-order equation over `F[X]` of total
jet degree at most `mu`, `Y₁` degree at most `M` and coefficient height at most `h`. For
`0 < D, ell`, `D < A ≤ n` and characteristic `0` or above `max D (jetDegree Q 1)`, one
exceptional set of challenges in `F` of size at most `hybridCurveOptimized n D ell A h mu M`
is fixed before every candidate. Outside it, every degree-`< D + 1` root over `F` of the
specialized equation with at least `A` agreements has exact power agreement over `F`. -/
theorem exists_baseExceptional_firstOrder_hybridCurve_optimized
    {F : Type*} [Field F] [DecidableEq F] {n D A h mu M ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) (hweight : jetTotalDegree Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M) (hheight : CoeffNatDegreeLE Q h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max D (jetDegree Q (1 : Fin 2)) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ hybridCurveOptimized n D ell A h mu M ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  let iota := algebraMap F (AlgebraicClosure F)
  let QE := MvPolynomial.map (Polynomial.mapRingHom iota) Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply hQ
    apply MvPolynomial.map_injective (Polynomial.mapRingHom iota)
      (Polynomial.map_injective iota iota.injective)
    simpa only [map_zero] using hz
  have hdegreeE : jetDegree QE (1 : Fin 2) ≤ jetDegree Q (1 : Fin 2) := jetDegree_map_le _ Q 1
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_firstOrder_hybridCurve_optimized domain values iota QE hQE
      ((jetTotalDegree_map_le _ Q).trans hweight) (hdegreeE.trans hdegree)
      (hheight.map_coefficients iota Q) hell hD hDA hAn
      (hchar.imp_right fun hc ↦ (max_le_max_left D hdegreeE).trans_lt hc)
  obtain ⟨baseExceptional, hbaseCard, hbase⟩ :=
    exists_exceptional_equation_powerAgreement_descend domain values iota Q (D + 1) A
      exceptional hgood
  exact ⟨baseExceptional,
    (show (baseExceptional.card : ℝ) ≤ exceptional.card by exact_mod_cast hbaseCard).trans hcard,
    hbase⟩

/-- The statement of `exists_baseExceptional_firstOrder_hybridCurve_optimized`, extended to
full message dimension `D + 1 = n`. There the bound is zero and the characteristic guard is not
needed. -/
theorem exists_baseExceptional_firstOrder_hybridCurve_including_fullDimension
    {F : Type*} [Field F] [DecidableEq F] {n D A h mu M ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) (hweight : jetTotalDegree Q ≤ mu)
    (hdegree : jetDegree Q (1 : Fin 2) ≤ M) (hheight : CoeffNatDegreeLE Q h)
    (hell : 0 < ell) (hD : 1 ≤ D) (hDA : D < A) (hAn : A ≤ n)
    (hchar : D + 1 = n ∨ ringChar F = 0 ∨
      max D (jetDegree Q (1 : Fin 2)) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        (if D + 1 = n then 0 else hybridCurveOptimized n D ell A h mu M) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  by_cases hfull : D + 1 = n
  · obtain ⟨_, _, hgood⟩ := exists_exactPower_fullDimension domain values
    refine ⟨∅, by simp [hfull], fun z _ P hP hagree _ ↦ ?_⟩
    rw [Fintype.card_fin] at hgood
    rw [hfull]
    exact hgood z P (by rw [← hfull]; exact_mod_cast hP) (by omega)
  · simpa only [hfull, ↓reduceIte] using
      exists_baseExceptional_firstOrder_hybridCurve_optimized domain values Q
        hQ hweight hdegree hheight hell hD hDA hAn (hchar.resolve_left hfull)

/-- Over an arbitrary field `F`, a strict surplus of shifted height slots over the row bound,
`firstOrderCurveShiftedRowSlotBound D A m M mu n ell h <
firstOrderCurveShiftedHeightSlotCount D A m M mu ell h`, gives optimized curve recovery. For
`0 < D, ell`, `0 < m * A` and `D < A ≤ n`, with full message dimension or characteristic `0` or
above `max D M`, one exceptional set of size at most `hybridCurveOptimized n D ell A h mu M`
(zero at full dimension) is fixed before every candidate. Outside it, every polynomial of
degree `< D + 1` with at least `A` agreements with the power-batched word has exact power
agreement. -/
theorem exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized
    {F : Type*} [Field F] [DecidableEq F] {n D A m M mu h ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (hD : 1 ≤ D) (hbudget : 0 < m * A)
    (hheight : firstOrderCurveShiftedRowSlotBound D A m M mu n ell h <
      firstOrderCurveShiftedHeightSlotCount D A m M mu ell h)
    (hell : 0 < ell) (hDA : D < A) (hAn : A ≤ n)
    (hchar : D + 1 = n ∨ ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        (if D + 1 = n then 0 else hybridCurveOptimized n D ell A h mu M) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    (k := D + 1) ell hD hbudget le_rfl domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
      (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i) hheight
  have hQ : cert.Q ≠ 0 := by
    intro hzero
    apply (cert.specialization_sound (RingHom.id F) 0).1
    rw [hzero, map_zero]
  have hweight : jetTotalDegree cert.Q ≤ mu := by
    rw [jetTotalDegree_le_iff]
    exact cert.totalJetDegree_le
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrder_hybridCurve_including_fullDimension domain values
      cert.Q hQ hweight cert.jetDegree_one_le cert.challengeDegree_le hell hD hDA hAn
      (hchar.imp_right fun hc ↦ hc.imp_right fun hc ↦
        (max_le_max_left D cert.jetDegree_one_le).trans_lt hc)
  refine ⟨exceptional, hcard, fun z hz P hP hagree ↦ hgood z hz P hP hagree ?_⟩
  have heval : Polynomial.eval₂RingHom (RingHom.id F) z = (Polynomial.aeval z).toRingHom :=
    Polynomial.ringHom_ext (fun _ ↦ by simp) (by simp)
  rw [challengeSpecialization, ← heval]
  refine (cert.specialization_sound (RingHom.id F) z).2 _ P hP hagree fun i hi ↦ ?_
  rw [eval₂_powerBatchedCoordinate_eq_powerBatchedWord]
  simpa using (Finset.mem_filter.mp hi).2

end

end ReedSolomon

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveBase
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveFinite
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Certificate

/-!
# Optimized curve recovery from a literal finite support inequality

A strict shifted-height slot inequality constructs the polynomial equation. Its specialization
is nonzero at every challenge and vanishes on every qualifying agreement subset. The recovery
theorem therefore requires neither an assumed interpolation certificate nor an assumed tail.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial PolynomialDifferential HiddenDerivative
open HiddenDerivative.SymbolicSeparantChain

noncomputable section

set_option autoImplicit false

open Classical in
/-- One numerical coefficient-versus-row inequality supplies optimized polynomial-curve MCA.
The exception set is fixed before the challenge, candidate, and every qualifying subset.
Both retention minima and the actual-degree maximum remain explicit in the bound. -/
theorem exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized
    {F : Type*} [Field F] {n D A m M mu h ell : ℕ}
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
        ∀ indices : Finset (Fin n), A ≤ indices.card →
          (∀ i ∈ indices, P.eval (domain i) = powerBatchedWord values z i) →
          HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    (k := D + 1) ell hD hbudget le_rfl domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
      (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i) hheight
  have hcharQ : D + 1 = n ∨ ringChar F = 0 ∨
      max D (jetDegree cert.Q (1 : Fin 2)) < ringChar F :=
    hchar.imp_right (fun hc ↦ hc.imp_right
      (fun hc' ↦ (max_le_max_left D cert.jetDegree_one_le).trans_lt hc'))
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_firstOrder_hybridCurve_base_including_fullDimension
      domain values cert.Q cert.nonzero cert.jetWeight_le cert.jetDegree_one_le
        cert.challengeDegree_le hell hD hDA hAn hcharQ
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hP indices hindices hagree
  have hsubset : indices ⊆ polynomialAgreementSet domain (powerBatchedWord values z) P := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hagree i hi⟩
  apply hgood z hz P hP (hindices.trans (Finset.card_le_card hsubset))
  have hroot := (cert.specialization_sound (RingHom.id F) z).2 indices P hP hindices
    (fun i hi ↦ by
      simpa only [RingHom.id_apply, Polynomial.eval₂_id, powerBatchedCoordinate_eval,
        powerBatchedWord] using hagree i hi)
  have heval : Polynomial.eval₂RingHom (RingHom.id F) z =
      (Polynomial.aeval z).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  simpa only [heval, challengeSpecialization] using hroot

open Classical in
/-- Complete-agreement form of the optimized finite-support curve theorem. -/
theorem exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized_fullAgreement
    {F : Type*} [Field F] {n D A m M mu h ell : ℕ}
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
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized
      domain values hD hbudget hheight hell hDA hAn hchar
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hP hagree
  exact hgood z hz P hP (polynomialAgreementSet domain (powerBatchedWord values z) P)
    hagree (fun i hi ↦ (Finset.mem_filter.mp hi).2)

end

end ReedSolomon

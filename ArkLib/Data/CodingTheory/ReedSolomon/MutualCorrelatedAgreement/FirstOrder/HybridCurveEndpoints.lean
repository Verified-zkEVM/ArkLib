/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveCertificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ConstantCode

/-!
# Endpoint dispatch for optimized finite-support curve recovery

Constant messages and the full code need neither an interpolation inequality nor a characteristic
guard. Only the nontrivial branch constructs a finite-support equation.

This dispatch supplies the endpoint cases used by the first-order capacity theorem in [DKTZ26]. It
keeps the constant-code result characteristic-free and gives the full code an empty exceptional
set before invoking the optimized hybrid theorem on the remaining branch.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], first-order endpoints and capacity MCA.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative

noncomputable section

open Classical in
/-- **Endpoint-complete optimized first-order curve recovery.**

The theorem covers every supplied agreeing subset, including constant messages and the full code.
The empty exceptional set takes priority when the constant code is also the full code. Only the
nontrivial branch consumes the finite-support height premise and positive-characteristic guard. -/
theorem exists_baseExceptional_firstOrderCurve_optimized_with_endpoints
    {F : Type*} [Field F] {n D A m M mu h ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (hell : 0 < ell) (hDA : D < A) (hAn : A ≤ n)
    (hbudget : 0 < D → D + 1 ≠ n → 0 < m * A)
    (hheight : 0 < D → D + 1 ≠ n →
      firstOrderCurveShiftedRowSlotBound D A m M mu n ell h <
        firstOrderCurveShiftedHeightSlotCount D A m M mu ell h)
    (hchar : D = 0 ∨ D + 1 = n ∨ ringChar F = 0 ∨ max D M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        (if D + 1 = n then 0 else if D = 0 then
          ((if A = 1 then ell * n.choose 2 else ell * n.choose 2 / (A - 1) : ℕ) : ℝ)
        else hybridCurveOptimized n D ell A h mu M) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        ∀ indices : Finset (Fin n), A ≤ indices.card →
          (∀ i ∈ indices, P.eval (domain i) = powerBatchedWord values z i) →
          HasExactPowerAgreement domain values (RingHom.id F) (D + 1) z P := by
  classical
  by_cases hfull : D + 1 = n
  · have hA : A = n := by omega
    obtain ⟨exceptional, hcard, hgood⟩ :=
      uniformExactPowerAgreement_fullDimension n ell domain values
    refine ⟨exceptional, ?_, ?_⟩
    · simpa only [if_pos hfull] using (show (exceptional.card : ℝ) ≤ 0 by
        exact_mod_cast hcard)
    · intro z hz P hP indices hindices hagree
      rw [hfull]
      apply hgood z hz P (by simpa only [← Nat.cast_add_one, hfull] using hP)
      have hsubset : indices ⊆ polynomialAgreementSet domain (powerBatchedWord values z) P := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hagree i hi⟩
      exact (show n ≤ indices.card by omega).trans (Finset.card_le_card hsubset)
  · by_cases hzero : D = 0
    · subst D
      obtain ⟨exceptional, hcard, hgood⟩ :=
        uniformExactPowerAgreement_constantCode domain values A (by omega)
      refine ⟨exceptional, ?_, ?_⟩
      · simpa only [if_neg hfull, ite_true] using (show (exceptional.card : ℝ) ≤
          ((if A = 1 then ell * n.choose 2 else ell * n.choose 2 / (A - 1) : ℕ) : ℝ) by
            exact_mod_cast hcard)
      · intro z hz P hP indices hindices hagree
        apply hgood z hz P hP
        apply hindices.trans (Finset.card_le_card ?_)
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hagree i hi⟩
    · have hD : 0 < D := by omega
      have hc : D + 1 = n ∨ ringChar F = 0 ∨ max D M < ringChar F :=
        hchar.resolve_left hzero
      obtain ⟨exceptional, hcard, hgood⟩ :=
        exists_baseExceptional_firstOrderCurve_of_heightSlotCount_optimized
          domain values hD (hbudget hD hfull) (hheight hD hfull) hell hDA hAn hc
      exact ⟨exceptional, by simpa only [if_neg hfull, if_neg hzero] using hcard, hgood⟩

end

end ReedSolomon

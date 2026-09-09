/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Ordinary.JohnsonProbability

/-!
# Numerical-first Johnson statements

These public forms fix all numerical parameters and hypotheses before the field and received
words. The exact integer threshold and the finite-field probability statement are separate.
-/

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

open Classical in
/-- Full agreement-set Johnson MCA in every characteristic, with numerical parameters fixed
before choosing the field. -/
theorem exists_exceptional_johnson_lineMCA_allChar
    (n D A : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n)
    {F : Type*} [Field F] (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ johnsonE0 n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  exact exists_exceptional_johnsonMCA domain f g hD hDn heta ha hthreshold hAn

open Classical in
/-- The exact ceiling threshold needs no additional denominator or degree assumptions. -/
theorem exists_exceptional_johnson_lineMCA_at_ceil
    (n D : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    {F : Type*} [Field F] (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        johnsonE0 n D (Nat.ceil (johnsonAgreement n D eta * n)) eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        Nat.ceil (johnsonAgreement n D eta * n) ≤
          (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  apply exists_exceptional_johnson_lineMCA_allChar n D _ eta hD hDn heta ha
    (Nat.le_ceil _) _ domain f g
  exact Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])

open Classical in
/-- Uniform affine-line failure probability at the exact Johnson threshold. -/
theorem johnson_lineMCA_probability
    (n D : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    {F : Type} [Field F] [Fintype F] (domain : Fin n ↪ F) :
    mcaError (AffineLineGenerator F) (code domain (D + 1))
        (1 - johnsonAgreement n D eta) ≤
      min 1 (ENNReal.ofReal
        (johnsonE0 n D (Nat.ceil (johnsonAgreement n D eta * n)) eta /
          (Fintype.card F : ℝ))) := by
  exact johnson_mcaError_le domain hD hDn heta ha

end ReedSolomon

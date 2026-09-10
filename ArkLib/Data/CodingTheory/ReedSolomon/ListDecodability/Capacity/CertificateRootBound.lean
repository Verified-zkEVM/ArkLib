/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Radius
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.SolutionEmbedding
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.ExtensionRootCount

/-!
# Root bounds from support-neutral interpolation certificates

This module turns any actual hidden-derivative interpolation certificate into a pointwise
polynomial-list bound.  It depends only on the certificate contract, its solution embedding, and
the generic extension-field root count.  In particular, it does not depend on how the certificate's
monomial support was constructed.
-/

@[expose] public section

open PolynomialDifferential

namespace ReedSolomon

open HiddenDerivative Polynomial

noncomputable section

/-- Actual construction witnesses give the coarse pointwise root-count bound. Neither an exact
interpolation-space membership premise nor a separately assumed list bound is required. -/
theorem HiddenDerivativeInterpolationCertificate.agreeingPolynomials_encard_le
    {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction :
      HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received) :
    (agreeingPolynomials domain k A received).encard ≤
      (2 * (d + 1) * q ^ (3 * d + 2) : ℕ) := by
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hlarge : 2 * q ^ 2 ≤ q ^ 3 := by
    calc
      2 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hq
      _ = q ^ 3 := by ring
  have hRoots := natCard_boundedSolution_le_extension_pow_of_weightedDegree
    construction.interpolant 3 (q ^ 2) (by decide) construction.nonzero
    construction.below_characteristic
    (by simpa only [Nat.card_zmod] using
      construction.weighted_degree_lt.le.trans construction.contact_budget_le)
    (by simpa only [Nat.card_zmod] using hlarge)
  have hRootsQ : Nat.card (BoundedSolution construction.interpolant
      (construction.ambientDim - 1)) ≤ 2 * (d + 1) * q ^ 2 * q ^ (3 * d) := by
    simpa only [Nat.card_zmod] using hRoots
  have hRoots' : Nat.card (BoundedSolution construction.interpolant
      (construction.ambientDim - 1)) ≤ 2 * (d + 1) * q ^ (3 * d + 2) := by
    convert hRootsQ using 1
    rw [pow_add, pow_mul]
    ring
  calc
    (agreeingPolynomials domain k A received).encard
        ≤ ENat.card (BoundedSolution construction.interpolant (construction.ambientDim - 1)) :=
      ENat.card_le_card_of_injective construction.solutionEmbedding.injective
    _ = (Nat.card (BoundedSolution construction.interpolant
        (construction.ambientDim - 1)) : ℕ∞) := ENat.card_eq_coe_natCard _
    _ ≤ (2 * (d + 1) * q ^ (3 * d + 2) : ℕ) := by
      exact_mod_cast hRoots'

end
end ReedSolomon

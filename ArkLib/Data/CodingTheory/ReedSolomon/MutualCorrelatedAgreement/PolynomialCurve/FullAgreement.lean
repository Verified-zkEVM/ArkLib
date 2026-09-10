/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.GraphLine
/-!
# Exact correlated agreement for power batching

The constituent polynomials live over the received-word field, even when the challenge
is selected in an extension field. Exactness means equality of the entire agreement set,
not merely existence of a common subset of a prescribed size.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- A close polynomial is exactly a power combination of base-field messages, and its full
agreement set is exactly their common agreement set.

The tuple has `ℓ + 1` constituents, corresponding to the weights `1,z,…,z^ℓ`. Each constituent
has degree below `k`. The scalar embedding `ι` is explicit so the statement supports both
extension-field geometry and the final base-field theorem. -/
def HasExactPowerAgreement [DecidableEq E] (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E) (k : ℕ) (z : E) (Q : E[X]) : Prop :=
  ∃ P : Fin (ℓ + 1) → F[X],
    -- All constituent messages belong to the original Reed–Solomon message space.
    (∀ t, (P t).degree < k) ∧
    -- Their power combination is the given polynomial, not merely the same codeword.
    Q = powerBatchedPolynomial (fun t ↦ (P t).map ι) z ∧
    -- No accidental agreements remain at this challenge.
    polynomialAgreementSet (mappedDomain domain ι)
      (powerBatchedWord (fun t i ↦ ι (w t i)) z) Q =
      commonCurveAgreementSet domain w P

/-- Scalar extension commutes with power batching the received words. -/
theorem powerBatchedWord_map (w : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E) (z : F) :
    powerBatchedWord (fun t i ↦ ι (w t i)) (ι z) = fun i ↦ ι (powerBatchedWord w z i) := by
  funext i
  simp [powerBatchedWord, map_sum, map_mul, map_pow]

/-- Scalar extension commutes with power batching the constituent messages. -/
theorem powerBatchedPolynomial_map (P : Fin (ℓ + 1) → F[X]) (ι : F →+* E) (z : F) :
    (powerBatchedPolynomial P z).map ι =
      powerBatchedPolynomial (fun t ↦ (P t).map ι) (ι z) := by
  simp [powerBatchedPolynomial, Polynomial.smul_eq_C_mul, Polynomial.map_sum]

end ReedSolomon

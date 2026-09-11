/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.UniformPowerAgreement
/-!
# Constant-code agreement on polynomial received curves

Constant messages require no characteristic hypothesis. Their agreement sets are disjoint, so
the exact list has size at most `n / A`. Polynomial-curve correlated agreement additionally uses
collision counting between received coordinate tuples.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F] {n ℓ : ℕ}

/-- For every challenge on a polynomial received curve, the complete constant-message list has
cardinality at most `n / A`. This includes the zero polynomial and works over arbitrary fields. -/
theorem exists_constantCode_list (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (z : F) (A : ℕ) (hA : 0 < A) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain (powerBatchedWord w z) 1 A) ∧
      list.card ≤ n / A := by
  obtain ⟨list, hlist, hincidence⟩ :=
    exists_closePolynomial_finset_with_incidence_bound
      domain (powerBatchedWord w z) (show 1 ≤ A by omega)
  refine ⟨list, hlist, (Nat.le_div_iff_mul_le hA).2 ?_⟩
  simpa using hincidence

end

end ReedSolomon

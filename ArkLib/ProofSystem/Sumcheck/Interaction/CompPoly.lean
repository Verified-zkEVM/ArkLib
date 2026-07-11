/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CompPoly.Basic
import ArkLib.ProofSystem.Sumcheck.Interaction.CompPolyHelpers

/-!
# CompPoly Bridge for Sum-Check

This module connects ArkLib's degree-bounded Sumcheck wrappers to the reusable
CompPoly multivariate polynomial operations.
-/

open CompPoly CPoly Std

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-! ## ArkLib degree-bounded wrapper lemmas -/

/-- `partialEvalFirst` preserves ArkLib's individual-degree predicate. -/
theorem partialEvalFirst_individualDegreeLE [Nontrivial R] {deg : ℕ} (a : R)
    (p : CMvPolynomial (n + 1) R)
    (hDeg : IndividualDegreeLE (R := R) deg p) :
    IndividualDegreeLE (R := R) deg (partialEvalFirst a p) := by
  intro i mono hmono
  exact partialEvalFirst_degreeOf_le (R := R) (n := n) (deg := deg) a i p
    (fun mono hmono => hDeg i.succ mono hmono) mono hmono

end CPoly.CMvPolynomial

/-! ## Sum-check prover residual state -/

namespace Sumcheck

/-- The prover's residual polynomial state during sum-check execution.

After round `i`, the prover holds a polynomial in `k` remaining variables
where `k = n - i`, with individual degree at most `deg`. -/
structure ResidualPoly (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] (deg : ℕ) where
  numVars : ℕ
  poly : CMvPolynomial numVars R
  degreeBound : CPoly.CMvPolynomial.IndividualDegreeLE (R := R) deg poly

end Sumcheck

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.IndexedDomain
public import ArkLib.ProofSystem.Sumcheck.Impl.IndexedProjection

/-! # Computable honest projections over indexed domains

`Sumcheck.Impl.IndexedProjection` computes the honest round message on CompPoly's carriers.
This module relates that computation to the indexed projection `projectedRoundPolynomial` of the
Sumcheck core, for every domain map, including one with repeated points. It does not import
`Sumcheck.Spec`.
-/

@[expose] public section

namespace Sumcheck.Computable
open CPoly CompPoly Finset Polynomial MvPolynomial
open CPoly.CMvPolynomial
variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  {n d deg : ℕ}

/-- The mathematical interpretation retains every individual degree bound. It is
`Impl.Computable.toRestrictDegree`. -/
abbrev toPolynomial (poly : CMvPolynomial n R) (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    R⦃≤ deg⦄[X Fin n] :=
  Impl.Computable.toRestrictDegree poly hpoly

/-- The computed enumeration interprets to the indexed honest projection of the Sumcheck core. -/
theorem indexedRoundPolynomial_toPoly (D : Fin d → R) (i : Fin (n + 1))
    (c : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    (Impl.Computable.indexedRoundPolynomial D i c poly).toPoly =
      (projectedRoundPolynomial D i c (toPolynomial poly hpoly)).val := by
  rw [Impl.Computable.indexedRoundPolynomial_toPoly]
  rfl

/-- The computed honest message for the indexed domain `D`. It is
`Impl.Computable.indexedMessage`. -/
abbrev projectedMessage (D : Fin d → R) {n : ℕ} (i : Fin n) (c : Fin i.castSucc → R)
    (poly : CMvPolynomial n R) (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    Impl.Representation.Message R deg :=
  Impl.Computable.indexedMessage D i c poly hpoly

/-- Interpreting the computed array gives exactly the indexed honest message. -/
theorem projectedMessage_toMessage (D : Fin d → R) (i : Fin n)
    (c : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    Impl.Representation.toMessage R deg (projectedMessage D i c poly hpoly) =
      projectedRoundPolynomial D i c (toPolynomial poly hpoly) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    apply Subtype.ext
    rw [Impl.Representation.toMessage_val]
    exact indexedRoundPolynomial_toPoly D i c poly hpoly

/-- Runtime Horner evaluation answers exactly the mathematical honest projection. -/
theorem projectedMessage_evaluate (D : Fin d → R) (i : Fin n)
    (c : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) (r : R) :
    Impl.Representation.evaluate R deg (projectedMessage D i c poly hpoly) r =
      (projectedRoundPolynomial D i c (toPolynomial poly hpoly)).val.eval r := by
  rw [Impl.Representation.evaluate_eq, projectedMessage_toMessage]

end Sumcheck.Computable

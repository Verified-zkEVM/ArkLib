/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Flattening
public import ArkLib.ToMathlib.MvPolynomial.OrdinaryFactorSeparable

/-!
# The positive-`Y₁` squarefree product with a retained challenge

After retaining the coefficient challenge as an actual coordinate, we swap `Y₁` into the
distinguished root position.  Factorization then retains the `Y₁`-independent content and
forms the distinct positive-`Y₁` product.  The latter is separable over the fraction field in
all remaining coordinates under the precise manuscript characteristic guard.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

noncomputable section

variable {F D : Type*} [Field F] [CommRing D] [IsDomain D]

/-- In flattened coordinates, swap `Y₁` with the distinguished challenge coordinate. -/
def flattenedRootFirstEquiv : Option (JetVariable 1) ≃ Option (JetVariable 1) :=
  Equiv.swap none (some (some 1))

/-- A challenge-retaining first-order equation with `Y₁` in the distinguished root slot. -/
def flattenedRootFirst (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (Option (JetVariable 1)) F :=
  renameEquiv F flattenedRootFirstEquiv (flattenFirstOrderChallenge Q)

@[simp]
theorem flattenedRootFirst_ne_zero_iff (Q : DifferentialPolynomial F[X] 1) :
    flattenedRootFirst Q ≠ 0 ↔ Q ≠ 0 := by
  change (renameEquiv F flattenedRootFirstEquiv) (flattenFirstOrderChallenge Q) ≠
      (renameEquiv F flattenedRootFirstEquiv) 0 ↔ Q ≠ 0
  rw [(renameEquiv F flattenedRootFirstEquiv).injective.ne_iff,
    flattenFirstOrderChallenge_ne_zero_iff]

theorem flattenedRootFirst_rootDegree_le (Q : DifferentialPolynomial F[X] 1) :
    degreeOf none (flattenedRootFirst Q) ≤ degreeOf (some (1 : Fin 2)) Q := by
  have hrename := degreeOf_rename_of_injective
    (p := flattenFirstOrderChallenge Q) flattenedRootFirstEquiv.injective
    (some (some (1 : Fin 2)))
  simpa only [flattenedRootFirst, renameEquiv_apply, flattenedRootFirstEquiv,
    Equiv.swap_apply_right] using
      hrename.le.trans (flattenFirstOrderChallenge_yOneDegree_le Q)

/-- The retained `Y₁`-independent content. -/
def flattenedContent (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (Option (JetVariable 1)) F :=
  ordinaryContent (flattenedRootFirst Q)

/-- The distinct positive-`Y₁` factor product. -/
def flattenedPositiveRootProduct (Q : DifferentialPolynomial F[X] 1) :
    MvPolynomial (Option (JetVariable 1)) F :=
  ordinaryRootProduct (flattenedRootFirst Q)

theorem flattenedContent_rootDegree (Q : DifferentialPolynomial F[X] 1) :
    degreeOf none (flattenedContent Q) = 0 :=
  degreeOf_ordinaryContent_none (flattenedRootFirst Q)

theorem flattenedContent_ne_zero (Q : DifferentialPolynomial F[X] 1) :
    flattenedContent Q ≠ 0 :=
  ordinaryContent_ne_zero (flattenedRootFirst Q)

theorem flattenedPositiveRootProduct_ne_zero (Q : DifferentialPolynomial F[X] 1) :
    flattenedPositiveRootProduct Q ≠ 0 :=
  ordinaryRootProduct_ne_zero (flattenedRootFirst Q)

/-- Content and positive-root product retain the exact zero locus after every domain map. -/
theorem flattened_split_zero_iff
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0)
    (f : MvPolynomial (Option (JetVariable 1)) F →+* D) :
    f (flattenedContent Q * flattenedPositiveRootProduct Q) = 0 ↔
      f (flattenedRootFirst Q) = 0 := by
  exact ordinary_split_zero_iff (flattenedRootFirst Q)
    (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ) f

/-- Distinct positive factors retain the source `Y₁` cap. -/
theorem flattened_factorRootDegrees_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) :
    ∑ a ∈ ordinaryRootFactorClasses (flattenedRootFirst Q),
        degreeOf none (ordinaryFactorRepresentative a) ≤
      degreeOf (some (1 : Fin 2)) Q := by
  exact (ordinary_root_degree_sum_le (flattenedRootFirst Q)
    (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ)).trans
      (flattenedRootFirst_rootDegree_le Q)

/-- The retained content and positive factors share the challenge-height budget. -/
theorem flattened_content_add_factorChallengeDegrees_le
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0)
    {H : ℕ} (hheight : ChallengeHeightLE Q H) :
    degreeOf (some (some (1 : Fin 2))) (flattenedContent Q) +
        ∑ a ∈ ordinaryRootFactorClasses (flattenedRootFirst Q),
          degreeOf (some (some (1 : Fin 2))) (ordinaryFactorRepresentative a) ≤ H := by
  have hfactor := ordinary_degree_sum_le (flattenedRootFirst Q)
    (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ) (some (some (1 : Fin 2)))
  have hrename := degreeOf_rename_of_injective
    (p := flattenFirstOrderChallenge Q) flattenedRootFirstEquiv.injective none
  have hchallenge :
      degreeOf (some (some (1 : Fin 2))) (flattenedRootFirst Q) ≤ H := by
    simpa only [flattenedRootFirst, renameEquiv_apply, flattenedRootFirstEquiv,
      Equiv.swap_apply_left] using
        hrename.le.trans (flattenFirstOrderChallenge_challengeDegree_le Q hheight)
  exact hfactor.trans hchallenge

/-- The positive-root product is separable over the fraction field in all other coordinates. -/
theorem flattenedPositiveRootProduct_map_fraction_separable
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) {M : ℕ}
    (hdegree : degreeOf (some (1 : Fin 2)) Q ≤ M)
    (hchar : ringChar F = 0 ∨ M < ringChar F) :
    ((ordinaryRootPolynomial (flattenedRootFirst Q)).map
      (algebraMap (MvPolynomial (JetVariable 1) F)
        (FractionRing (MvPolynomial (JetVariable 1) F)))).Separable := by
  apply ordinaryRootPolynomial_map_fraction_separable (flattenedRootFirst Q)
    (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ)
  rcases hchar with hzero | hpositive
  · exact Or.inl hzero
  · exact Or.inr ((flattenedRootFirst_rootDegree_le Q).trans_lt
      (hdegree.trans_lt hpositive))

/-- The actual padded derivative resultant of the positive product is nonzero. -/
theorem flattenedPositiveRootProduct_resultant_ne_zero
    (Q : DifferentialPolynomial F[X] 1) (hQ : Q ≠ 0) {M : ℕ}
    (hdegree : degreeOf (some (1 : Fin 2)) Q ≤ M)
    (hchar : ringChar F = 0 ∨ M < ringChar F) :
    paddedDerivativeResultant (ordinaryRootPolynomial (flattenedRootFirst Q))
        (degreeOf none (flattenedPositiveRootProduct Q)) ≠ 0 := by
  apply paddedDerivativeResultant_ordinaryRootPolynomial_ne_zero
    (flattenedRootFirst Q) (flattenedRootFirst_ne_zero_iff Q |>.mpr hQ)
  rcases hchar with hzero | hpositive
  · exact Or.inl hzero
  · exact Or.inr ((flattenedRootFirst_rootDegree_le Q).trans_lt
      (hdegree.trans_lt hpositive))

end

end ReedSolomon.FirstOrder.Squarefree

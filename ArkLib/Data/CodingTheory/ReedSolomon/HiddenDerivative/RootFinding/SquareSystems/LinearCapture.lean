/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.CodimensionOne
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.EvaluationTail
/-!
# Linear core of evaluation-and-tail square capture

The invertible evaluation-and-tail map preserves injectivity of the Taylor coefficient
differential on the hypersurface tangent space. Coordinate selection then chooses `r` actual
evaluation or tail rows which, together with the hypersurface normal, form an invertible square
linear system. This includes `k <= r`, since tail rows remain in the selectable pool.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

open Function

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- Evaluation and tail coordinates, indexed by their disjoint-union pool. -/
def evaluationTailPoolMap (K k : ℕ) (hk : k ≤ K) (center : F)
    (points : Fin k ↪ F) : (Fin K → F) →ₗ[F] (Fin k ⊕ Fin (K - k) → F) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin (K - k)) F F).symm.toLinearMap.comp
    (evaluationTailMap K k hk center points)

/-- The pool-indexed form of the evaluation-and-tail map is injective. -/
theorem evaluationTailPoolMap_injective (K k : ℕ) (hk : k ≤ K) (center : F)
    (points : Fin k ↪ F) : Injective (evaluationTailPoolMap K k hk center points) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin (K - k)) F F).symm.injective.comp
    (evaluationTailMap_injective K k hk center points)

/-- If the ambient coefficient differential is injective on a smooth hypersurface tangent space,
some `r` actual evaluation-or-tail rows combine with the normal into an injective square map. -/
theorem exists_evaluationTail_squareRows {K k r : ℕ} (hk : k ≤ K) (center : F)
    (points : Fin k ↪ F) (normal : W →ₗ[F] F) (coefficients : W →ₗ[F] (Fin K → F))
    (hdim : Module.finrank F W = r + 1) (hnormal : normal ≠ 0)
    (hcoefficients : Injective (coefficients.comp normal.ker.subtype)) :
    ∃ selected : Fin r ↪ (Fin k ⊕ Fin (K - k)),
      Injective (normalSelectedMap normal
        ((evaluationTailPoolMap K k hk center points).comp coefficients) selected) := by
  apply exists_injective_normalSelectedMap normal
    ((evaluationTailPoolMap K k hk center points).comp coefficients) hdim hnormal
  intro x y hxy
  apply hcoefficients
  apply evaluationTailPoolMap_injective K k hk center points
  exact hxy

end ReedSolomon.HiddenDerivative.SquareSystems

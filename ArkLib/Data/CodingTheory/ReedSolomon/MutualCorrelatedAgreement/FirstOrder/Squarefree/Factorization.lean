/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Types
public import ArkLib.ToMathlib.MvPolynomial.OrdinaryFactorDegrees

/-!
# The squarefree positive-`Y₁` product of a first-order equation

We put `Y₁` in the distinguished `none` coordinate by swapping it with the independent
coordinate.  The generic ordinary-factor API then splits a nonzero first-order equation into
root-independent content and the squarefree product of all irreducible factors having positive
`Y₁` degree.  This retains content rather than silently discarding it.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial PolynomialDifferential

noncomputable section

variable {F D : Type*} [Field F] [CommRing D] [IsDomain D]

/-- Root-first coordinates: `Y₁` becomes `none`, while `X` moves to `some 1` and `Y₀`
remains `some 0`. -/
def rootFirstEquiv : JetVariable 1 ≃ Option (Fin 2) :=
  Equiv.swap none (some 1)

/-- A first-order equation written with `Y₁` as its distinguished root variable. -/
def rootFirst (Q : DifferentialPolynomial F 1) : MvPolynomial (Option (Fin 2)) F :=
  renameEquiv F rootFirstEquiv Q

@[simp]
theorem rootFirst_ne_zero_iff (Q : DifferentialPolynomial F 1) :
    rootFirst Q ≠ 0 ↔ Q ≠ 0 := by
  change (renameEquiv F rootFirstEquiv) Q ≠ (renameEquiv F rootFirstEquiv) 0 ↔ Q ≠ 0
  exact (renameEquiv F rootFirstEquiv).injective.ne_iff

theorem totalDegree_rootFirst (Q : DifferentialPolynomial F 1) :
    (rootFirst Q).totalDegree = Q.totalDegree := by
  exact totalDegree_renameEquiv rootFirstEquiv Q

theorem rootDegree_rootFirst (Q : DifferentialPolynomial F 1) :
    degreeOf none (rootFirst Q) = degreeOf (some 1) Q := by
  simpa only [rootFirst, renameEquiv_apply, rootFirstEquiv, Equiv.swap_apply_right] using
    degreeOf_rename_of_injective (p := Q) rootFirstEquiv.injective (some (1 : Fin 2))

/-- The retained content, in root-first coordinates. -/
def content (Q : DifferentialPolynomial F 1) : MvPolynomial (Option (Fin 2)) F :=
  ordinaryContent (rootFirst Q)

/-- The squarefree product of all factors with positive `Y₁` degree, in root-first
coordinates. -/
def positiveRootProduct (Q : DifferentialPolynomial F 1) :
    MvPolynomial (Option (Fin 2)) F :=
  ordinaryRootProduct (rootFirst Q)

theorem content_ne_zero (Q : DifferentialPolynomial F 1) : content Q ≠ 0 :=
  ordinaryContent_ne_zero (rootFirst Q)

theorem positiveRootProduct_ne_zero (Q : DifferentialPolynomial F 1) :
    positiveRootProduct Q ≠ 0 :=
  ordinaryRootProduct_ne_zero (rootFirst Q)

/-- The retained content is genuinely independent of `Y₁`. -/
theorem content_rootDegree (Q : DifferentialPolynomial F 1) :
    degreeOf none (content Q) = 0 :=
  degreeOf_ordinaryContent_none (rootFirst Q)

/-- The retained content and positive-root product have the same zero locus as the original
equation after every map to a domain. -/
theorem split_zero_iff
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0)
    (f : MvPolynomial (Option (Fin 2)) F →+* D) :
    f (content Q * positiveRootProduct Q) = 0 ↔ f (rootFirst Q) = 0 := by
  exact ordinary_split_zero_iff (rootFirst Q) (rootFirst_ne_zero_iff Q |>.mpr hQ) f

/-- Content and all distinct positive-`Y₁` factors share the original total-degree budget. -/
theorem content_add_factorTotalDegrees_le
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    (content Q).totalDegree +
        ∑ a ∈ ordinaryRootFactorClasses (rootFirst Q),
          (ordinaryFactorRepresentative a).totalDegree ≤ Q.totalDegree := by
  rw [← totalDegree_rootFirst Q]
  exact ordinary_totalDegree_sum_le (rootFirst Q) (rootFirst_ne_zero_iff Q |>.mpr hQ)

/-- The positive-root squarefree product alone stays within the original total-degree budget. -/
theorem positiveRootProduct_totalDegree_le
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    (positiveRootProduct Q).totalDegree ≤ Q.totalDegree := by
  rw [← totalDegree_rootFirst Q]
  exact totalDegree_ordinaryRootProduct_le (rootFirst Q) (rootFirst_ne_zero_iff Q |>.mpr hQ)

/-- Distinct positive factors spend no more `Y₁` degree than the source equation. -/
theorem factorRootDegrees_le
    (Q : DifferentialPolynomial F 1) (hQ : Q ≠ 0) :
    ∑ a ∈ ordinaryRootFactorClasses (rootFirst Q),
        degreeOf none (ordinaryFactorRepresentative a) ≤ degreeOf (some 1) Q := by
  rw [← rootDegree_rootFirst Q]
  exact ordinary_root_degree_sum_le (rootFirst Q) (rootFirst_ne_zero_iff Q |>.mpr hQ)

end

end ReedSolomon.FirstOrder.Squarefree

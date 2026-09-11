/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Bounds

/-!
# The content-resultant singular tail

For the squarefree positive-`Y₁` product `A`, the singular solutions are routed to the product
of the retained `Y₁`-independent content `U` and the padded derivative resultant.  The matrix
sizes in `separableResultant` are the original sizes, so the routing theorem remains valid when a
coefficient specialization lowers the actual `Y₁` degree.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open Polynomial

noncomputable section

variable {R S : Type*} [CommRing R]

/-- The ordinary singular-tail equation: retained content times the derivative resultant. -/
def singularTail (U : R[X]) (A : R[X][X]) (r : ℕ) : R[X] :=
  U * separableResultant A r

/-- The exact ordinary-degree bound for the singular tail.  The coefficient triangle is the
formal version of `deg_Y₀ aᵢ ≤ j - i`. -/
theorem natDegree_singularTail_le
    (U : R[X]) (A : R[X][X]) {B M bU j r : ℕ}
    (hr : 0 < r) (hrj : r ≤ j) (hrM : r ≤ M) (hMB : M ≤ B)
    (hcontent : U.natDegree ≤ bU) (hbudget : bU + j ≤ B)
    (hdegree : A.natDegree = r)
    (hcoeff : ∀ i, i ≤ r → i + (A.coeff i).natDegree ≤ j) :
    (singularTail U A r).natDegree ≤ ordinaryDegreeEnvelope B M := by
  have hresultant := natDegree_separableResultant_add_sq_le_of_le A hr hdegree hcoeff
  have htail := content_add_resultantDegree_le
    (B := B) (M := M) (bU := bU) (j := j) (r := r)
    (d := (separableResultant A r).natDegree)
    hr hrj hrM hMB hbudget hresultant
  exact natDegree_mul_le.trans ((Nat.add_le_add_right hcontent _).trans htail)

/-- Every common root of a specialized equation and its specialized derivative kills the
original-size singular tail.  In particular, no specialized degree equality is required. -/
theorem singularTail_map_eq_zero_of_common_root
    [IsDomain R] [CommRing S] [IsDomain S]
    (U : R[X]) (A : R[X][X]) {r : ℕ} (hr : 0 < r) (hdegree : A.natDegree ≤ r)
    (f : R[X] →+* S) (u : S)
    (hroot : (A.map f).eval u = 0)
    (hderivative : (A.map f).derivative.eval u = 0) :
    f (singularTail U A r) = 0 := by
  rw [singularTail, map_mul,
    separableResultant_map_eq_zero_of_common_root A hr hdegree f u hroot hderivative,
    mul_zero]

end

end ReedSolomon.FirstOrder.Squarefree

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix

/-!
# Local constraint matrix acceptance tests

At `d = 0` and `m = 1`, with one point `(0, r)` and the single column `Y₀`, the entry at the
constant exponent is `r`, so for `r = 1` the kernel is zero. The row at `E²` has contact order `0`
but lies above the column's jet degree, so its entry vanishes and it is not a supported row. For a
received line, every entry in the column of `Y₀^(y₀)` has challenge degree at most `y₀`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped Polynomial Matrix

namespace ConstraintMatrixTest

/-- The row at the point `0` and the constant exponent, of contact order `0`. -/
def row₀ : Fin 1 × LowContactIndex 0 1 := (0, ⟨0, by simp [localContactOrder]⟩)

/-- The row at the point `0` and the exponent `E²`, of contact order `0` since `d = 0`. -/
noncomputable def rowE : Fin 1 × LowContactIndex 0 1 :=
  (0, ⟨Finsupp.single (localE 0) 2, by simp [localContactOrder_eq, localT, localAux]⟩)

/-- The single column `Y₀` at `d = 0`. -/
def colY : Fin 1 → SourceColumn 0 := fun _ => ⟨0, 1, ![]⟩

/-- The entry of `Y₀` at the constant exponent is the received value. -/
theorem entry_row₀ {R : Type*} [CommRing R] (r : R) :
    localConstraintMatrix 1 (fun _ : Fin 1 => (0 : R)) (fun _ => r) colY row₀ 0 = r := by
  change (unscaledLocalSubstitution 0 (0 : R) r (colY 0).polynomial).coeff 0 = r
  rw [SourceColumn.polynomial_eq_sourceMonomial, ← constantCoeff_eq]
  simp [colY, sourceMonomial, localCorrection]

/-- The matrix entry is the constant coefficient of the projected local constraint. -/
example (r : ℚ) :
    localConstraintMatrix 1 (fun _ : Fin 1 ↦ (0 : ℚ)) (fun _ ↦ r) colY row₀ 0 =
      (localConstraintAt 1 0 r (colY 0).polynomial).coeff 0 :=
  localConstraintMatrix_apply_eq_localConstraintAt_coeff 1 _ _ colY row₀ 0

/-- With received value `1`, the kernel is zero. -/
example (v : Fin 1 → ℚ)
    (hv : localConstraintMatrix 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 1) colY *ᵥ v = 0) :
    v = 0 := by
  have h := congrFun hv row₀
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, entry_row₀, one_mul,
    Pi.zero_apply] at h
  funext j
  fin_cases j
  exact h

/-- The kernel condition is the local constraint condition on the interpolant. -/
example (v : Fin 1 → ℚ) :
    localConstraintMatrix 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 1) colY *ᵥ v = 0 ↔
      SatisfiesLocalConstraints 1 0 1 (SourceColumn.interpolant colY v) := by
  simpa [Fin.forall_fin_one] using
    localConstraintMatrix_mulVec_eq_zero_iff 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => 1) colY v

/-- The constant row is supported when the received value is nonzero. -/
example (r : ℚ) (hr : r ≠ 0) :
    row₀ ∈ localConstraintSupportedRows 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => r) colY :=
  (mem_localConstraintSupportedRows_iff 1 _ _ colY row₀).mpr ⟨0, by rwa [entry_row₀]⟩

/-- The row at `E²` lies above the jet degree `1` of `Y₀`, so its entry vanishes. -/
theorem entry_rowE (center received : ℚ) :
    localConstraintMatrix 1 (fun _ : Fin 1 => center) (fun _ => received) colY rowE 0 = 0 :=
  localConstraintMatrix_eq_zero_of_lt 1 _ _ colY rowE 0
    (by simp [colY, rowE, Finsupp.weight_single, localJetDegreeWeight, localAux])

/-- The row at `E²` is not supported. -/
example (center received : ℚ) :
    rowE ∉ localConstraintSupportedRows 1 (fun _ : Fin 1 => center) (fun _ => received) colY := by
  rw [mem_localConstraintSupportedRows_iff]
  rintro ⟨j, hj⟩
  fin_cases j
  exact hj (entry_rowE center received)

/-- Restricting to the supported rows keeps the rank. -/
example (r : ℚ) :
    ((supportedLocalConstraintMatrix 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => r) colY).map
      (RingHom.id ℚ)).rank =
      ((localConstraintMatrix 1 (fun _ : Fin 1 => (0 : ℚ)) (fun _ => r) colY).map
        (RingHom.id ℚ)).rank :=
  rank_map_supportedLocalConstraintMatrix _ 1 _ _ colY

/-- For a received line `f i + Z g i`, every entry in the column of `Y₀^(y₀)` has challenge
degree
at most `y₀`. -/
example {F : Type*} [Field F] {d n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) (row : Fin n × LowContactIndex d m) (j : Fin N) :
    (localConstraintMatrix m (fun i => Polynomial.C (centers i))
      (fun i => Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i)) columns row j).natDegree ≤
      (columns j).y₀ :=
  (natDegree_localConstraintMatrix_le m 1 centers
    (fun i => Polynomial.C (f i) + Polynomial.X * Polynomial.C (g i))
    (fun i => by compute_degree) columns row j).trans_eq (one_mul _)

end ConstraintMatrixTest

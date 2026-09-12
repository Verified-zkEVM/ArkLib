/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Multivariate.Substitution
public import ArkLib.ToCompPoly.Multivariate.Eval
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Executable linear coordinates for regular Taylor geometry

These substitutions consume a supplied coordinate matrix. Their evaluation and inverse-point
identities preserve the entire regular locus, without a projection-discriminant condition.
Selecting the matrix and producing the retained regular component remain separate obligations.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.Geometry

open CPoly CPoly.CMvPolynomial
open scoped BigOperators

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] {n : ℕ}

/-- The stored linear polynomial representing one row of a coordinate matrix. -/
def linearCoordinate (M : Matrix (Fin n) (Fin n) R) (i : Fin n) : CMvPolynomial n R :=
  ∑ j, C (M i j) * X j

/-- Substitute the supplied linear coordinates into a stored polynomial. -/
def projectPolynomial (M : Matrix (Fin n) (Fin n) R) (p : CMvPolynomial n R) :
    CMvPolynomial n R :=
  bind₁ (linearCoordinate M) p

/-- Coordinate polynomials evaluate to matrix multiplication on points. -/
theorem eval_linearCoordinate (M : Matrix (Fin n) (Fin n) R) (x : Fin n → R)
    (i : Fin n) : (linearCoordinate M i).eval x = (M.mulVec x) i := by
  simp [linearCoordinate, eval_sum, Matrix.mulVec, dotProduct]

/-- Conversion retains the actual linear polynomial, rather than merely its finite-field values. -/
theorem from_linearCoordinate (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    fromCMvPolynomial (linearCoordinate M i) =
      ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j := by
  simp [linearCoordinate, fromCMvPolynomial_sum,
    fromCMvPolynomial_C, fromCMvPolynomial_X]

/-- The executed substitution represents semantic substitution by the matrix rows. -/
theorem from_projectPolynomial (M : Matrix (Fin n) (Fin n) R) (p : CMvPolynomial n R) :
    fromCMvPolynomial (projectPolynomial M p) =
      MvPolynomial.aeval (fun i => ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j)
        (fromCMvPolynomial p) := by
  simp [projectPolynomial, fromCMvPolynomial_bind₁, from_linearCoordinate]

/-- Each projected coordinate has total degree at most one, including a zero matrix row. -/
theorem totalDegree_linearCoordinate_le [Nontrivial R] (M : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    (fromCMvPolynomial (linearCoordinate M i)).totalDegree ≤ 1 := by
  rw [from_linearCoordinate]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- Linear projection cannot increase the total degree of the stored polynomial. -/
theorem totalDegree_projectPolynomial_le [Nontrivial R] (M : Matrix (Fin n) (Fin n) R)
    (p : CMvPolynomial n R) :
    (fromCMvPolynomial (projectPolynomial M p)).totalDegree ≤
      (fromCMvPolynomial p).totalDegree := by
  classical
  rw [projectPolynomial, fromCMvPolynomial_bind₁]
  change (MvPolynomial.eval₂ MvPolynomial.C
    (fun i => fromCMvPolynomial (linearCoordinate M i)) (fromCMvPolynomial p)).totalDegree ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ e.support, (fromCMvPolynomial (linearCoordinate M i) ^ e i).totalDegree ≤
        ∑ i ∈ e.support, e i := by
      apply Finset.sum_le_sum
      intro i _
      simpa using (MvPolynomial.totalDegree_pow
        (fromCMvPolynomial (linearCoordinate M i)) (e i)).trans
          (Nat.mul_le_mul_left (e i) (totalDegree_linearCoordinate_le M i))
    _ = e.degree := rfl
    _ ≤ (fromCMvPolynomial p).totalDegree := Finset.le_sup he

/-- Evaluation commutes with the executed linear projection. -/
theorem eval_projectPolynomial (M : Matrix (Fin n) (Fin n) R) (p : CMvPolynomial n R)
    (x : Fin n → R) : (projectPolynomial M p).eval x = p.eval (M.mulVec x) := by
  rw [eval_equiv, from_projectPolynomial, eval_equiv]
  change MvPolynomial.aeval x (MvPolynomial.aeval _ _) =
    MvPolynomial.aeval (M.mulVec x) (fromCMvPolynomial p)
  rw [MvPolynomial.comp_aeval_apply]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct]

omit [BEq R] [LawfulBEq R] in
/-- A supplied right inverse recovers every original point. -/
theorem inverse_point_roundtrip (M N : Matrix (Fin n) (Fin n) R) (hMN : M * N = 1)
    (u : Fin n → R) : M.mulVec (N.mulVec u) = u := by
  rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]

/-- Pulling back along inverse coordinates preserves every polynomial value. -/
theorem eval_projectPolynomial_inverse (M N : Matrix (Fin n) (Fin n) R)
    (hMN : M * N = 1) (p : CMvPolynomial n R) (u : Fin n → R) :
    (projectPolynomial M p).eval (N.mulVec u) = p.eval u := by
  rw [eval_projectPolynomial, inverse_point_roundtrip M N hMN]

/-- The equation and separant define the same regular points after the coordinate change.
No condition on projection ramification is needed. -/
theorem regular_locus_iff (M N : Matrix (Fin n) (Fin n) R) (hMN : M * N = 1)
    (H S : CMvPolynomial n R) (u : Fin n → R) :
    ((projectPolynomial M H).eval (N.mulVec u) = 0 ∧
      (projectPolynomial M S).eval (N.mulVec u) ≠ 0) ↔
      (H.eval u = 0 ∧ S.eval u ≠ 0) := by
  rw [eval_projectPolynomial_inverse M N hMN, eval_projectPolynomial_inverse M N hMN]

end ReedSolomon.HiddenDerivative.FastTaylor.Geometry

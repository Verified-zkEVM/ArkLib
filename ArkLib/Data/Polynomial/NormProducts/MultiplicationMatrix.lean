/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Univariate.DivisionCorrectness
public import Mathlib.RingTheory.AdjoinRoot
public import ArkLib.ToMathlib.LinearAlgebra.FiniteFreeNorm

/-!
# Executable multiplication determinants for monic polynomial algebras

The columns are the remainders of `g * X^j` modulo the supplied monic polynomial.
Taking `R = CPolynomial E` produces stored polynomials in the projection parameter.
The implementation needs neither a field nor a reduced quotient. The explicit width permits
specialization without transporting executable matrices across degree equalities.
-/

@[expose] public section

namespace CompPoly.CPolynomial.NormProducts

open Polynomial

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- Compute the multiplication matrix in the first `n` monomials. Correct norm use requires
`n = h.toPoly.natDegree` and monicity of `h`. -/
def multiplicationMatrix (n : ℕ) (h g : CPolynomial R) : Matrix (Fin n) (Fin n) R :=
  fun i j => ((g * X ^ j.val).modByMonic h).coeff i.val

/-- The actual determinant producer, computed from monic-remainder matrix columns. -/
def norm (n : ℕ) (h g : CPolynomial R) : R :=
  (multiplicationMatrix n h g).det

/-- Polynomial reference for each matrix entry, rather than a supplied norm oracle. -/
theorem multiplicationMatrix_apply (n : ℕ) (h g : CPolynomial R) (hh : h.monic)
    (i j : Fin n) :
    multiplicationMatrix n h g i j =
      ((g.toPoly * Polynomial.X ^ j.val) %ₘ h.toPoly).coeff i.val := by
  rw [multiplicationMatrix, coeff_toPoly, modByMonic_toPoly_eq_modByMonic _ _ hh,
    toPoly_mul, toPoly_pow, X_toPoly]

/-- The executed columns are exactly the matrix of multiplication in the canonical monic
quotient basis. This quotient may have nilpotents. -/
theorem multiplicationMatrix_eq_leftMulMatrix (h g : CPolynomial R) (hh : h.monic) :
    multiplicationMatrix h.toPoly.natDegree h g =
      Algebra.leftMulMatrix (AdjoinRoot.powerBasisAux' ((monic_toPoly_iff h).mp hh))
        (AdjoinRoot.mk h.toPoly g.toPoly) := by
  ext i j
  rw [multiplicationMatrix_apply _ _ _ hh, Algebra.leftMulMatrix_eq_repr_mul]
  rw [show AdjoinRoot.powerBasisAux' ((monic_toPoly_iff h).mp hh) j =
    AdjoinRoot.root h.toPoly ^ j.val from
      (AdjoinRoot.powerBasis' ((monic_toPoly_iff h).mp hh)).basis_eq_pow j]
  change _ = (AdjoinRoot.powerBasisAux' ((monic_toPoly_iff h).mp hh)).repr
    (AdjoinRoot.mk h.toPoly g.toPoly * AdjoinRoot.root h.toPoly ^ j.val) i
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    AdjoinRoot.powerBasisAux'_repr_apply_to_fun, AdjoinRoot.modByMonicHom_mk]

/-- Refinement of the concrete determinant to the finite-free algebra norm. -/
theorem norm_eq_algebraNorm (h g : CPolynomial R) (hh : h.monic) :
    norm h.toPoly.natDegree h g =
      Algebra.norm R (AdjoinRoot.mk h.toPoly g.toPoly) := by
  rw [norm, multiplicationMatrix_eq_leftMulMatrix _ _ hh,
    ← Algebra.norm_eq_matrix_det (AdjoinRoot.powerBasisAux' ((monic_toPoly_iff h).mp hh))]

section Specialization

variable {S : Type*} [CommRing S]

/-- Every entry commutes with an arbitrary coefficient homomorphism. In particular no
projection discriminant or separability condition is needed. -/
theorem map_multiplicationMatrix (σ : R →+* S) (n : ℕ)
    (h g : CPolynomial R) (hh : h.monic) :
    σ.mapMatrix (multiplicationMatrix n h g) =
      fun i j : Fin n =>
        (((g.toPoly.map σ) * Polynomial.X ^ j.val) %ₘ (h.toPoly.map σ)).coeff i.val := by
  ext i j
  change σ (multiplicationMatrix n h g i j) = _
  rw [multiplicationMatrix_apply _ _ _ hh, ← Polynomial.coeff_map,
    Polynomial.map_modByMonic σ ((monic_toPoly_iff h).mp hh)]
  simp

/-- The determinant producer commutes with every specialization, even to a ramified fiber. -/
theorem map_norm (σ : R →+* S) (n : ℕ) (h g : CPolynomial R) (hh : h.monic) :
    σ (norm n h g) =
      Matrix.det (fun i j : Fin n =>
        (((g.toPoly.map σ) * Polynomial.X ^ j.val) %ₘ (h.toPoly.map σ)).coeff i.val) := by
  rw [norm, RingHom.map_det, map_multiplicationMatrix _ _ _ _ hh]

/-- The specialized determinant is the algebra norm in the entire specialized quotient. -/
theorem map_norm_eq_algebraNorm [Nontrivial S] (σ : R →+* S) (h g : CPolynomial R) (hh : h.monic) :
    σ (norm h.toPoly.natDegree h g) =
      Algebra.norm S (AdjoinRoot.mk (h.toPoly.map σ) (g.toPoly.map σ)) := by
  let hm := (monic_toPoly_iff h).mp hh
  let b := AdjoinRoot.powerBasisAux' (hm.map σ)
  rw [map_norm _ _ _ _ hh, Algebra.norm_eq_matrix_det b]
  have hd := hm.natDegree_map σ
  conv_rhs => rw [← Matrix.det_reindex_self (finCongr hd)]
  congr 1
  ext i j
  rw [Matrix.reindex_apply]
  change _ = Algebra.leftMulMatrix b
    (AdjoinRoot.mk (h.toPoly.map σ) (g.toPoly.map σ))
    ((finCongr hd).symm i) ((finCongr hd).symm j)
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change _ = b.repr (AdjoinRoot.mk (h.toPoly.map σ) (g.toPoly.map σ) *
    b ((finCongr hd).symm j)) ((finCongr hd).symm i)
  rw [show b ((finCongr hd).symm j) =
    AdjoinRoot.root (h.toPoly.map σ) ^ j.val from
      (AdjoinRoot.powerBasis' (hm.map σ)).basis_eq_pow ((finCongr hd).symm j)]
  change _ = (AdjoinRoot.powerBasisAux' (hm.map σ)).repr
    (AdjoinRoot.mk (h.toPoly.map σ) (g.toPoly.map σ) *
      AdjoinRoot.root (h.toPoly.map σ) ^ j.val) ((finCongr hd).symm i)
  rw [← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    AdjoinRoot.powerBasisAux'_repr_apply_to_fun, AdjoinRoot.modByMonicHom_mk]
  rfl

end Specialization

section FieldSpecialization

variable {K B : Type*} [Field K] [CommRing B] [Nontrivial B] [Algebra K B]

/-- Vanishing at any geometric point of the specialized fiber forces the computed norm to
vanish. The fiber is allowed to be nonreduced, so ramified fibers are retained. -/
theorem map_norm_eq_zero_of_point (σ : R →+* K) (h g : CPolynomial R) (hh : h.monic)
    (x : B) (hx : Polynomial.aeval x (h.toPoly.map σ) = 0)
    (gx : Polynomial.aeval x (g.toPoly.map σ) = 0) :
    σ (norm h.toPoly.natDegree h g) = 0 := by
  let hm := ((monic_toPoly_iff h).mp hh).map σ
  let := hm.finite_adjoinRoot
  rw [map_norm_eq_algebraNorm _ _ _ hh]
  apply Algebra.norm_eq_zero_of_algHom_eq_zero
    (AdjoinRoot.liftAlgHom (h.toPoly.map σ) (Algebra.ofId K B) x hx)
  change Polynomial.eval₂ (algebraMap K B) x (g.toPoly.map σ) = 0
  exact gx

/-- Generic coprimality ensures a nonzero norm, without requiring the quotient to be a
field or a domain. This applies to the function-field specialization of a component. -/
theorem norm_ne_zero_of_map_isCoprime (σ : R →+* K) (h g : CPolynomial R) (hh : h.monic)
    (hc : IsCoprime (h.toPoly.map σ) (g.toPoly.map σ)) :
    norm h.toPoly.natDegree h g ≠ 0 := by
  have hu : IsUnit (AdjoinRoot.mk (h.toPoly.map σ) (g.toPoly.map σ)) := by
    have hm := hc.map (AdjoinRoot.mk (h.toPoly.map σ))
    rw [AdjoinRoot.mk_self, isCoprime_zero_left] at hm
    exact hm
  have hn := (hu.map (Algebra.norm K)).ne_zero
  rw [← map_norm_eq_algebraNorm _ _ _ hh] at hn
  exact fun hz => hn (by rw [hz, map_zero])

end FieldSpecialization

/-- Compute the norm with its canonical width, derived from the input modulus. -/
def polynomialNorm (h g : CPolynomial R) : R := norm h.natDegree h g

/-- Input-to-output correctness of the canonical executable producer. -/
theorem polynomialNorm_eq_algebraNorm (h g : CPolynomial R) (hh : h.monic) :
    polynomialNorm h g = Algebra.norm R (AdjoinRoot.mk h.toPoly g.toPoly) := by
  rw [polynomialNorm, natDegree_toPoly, norm_eq_algebraNorm _ _ hh]

end CompPoly.CPolynomial.NormProducts

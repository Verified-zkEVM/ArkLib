/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.Polynomial.Interface
import CompPoly.Data.Polynomial.MonomialBasis
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Henselian
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Basic

open Polynomial Matrix Code LinearCode

variable {F ι ι' : Type*}

section

namespace Vandermonde

/-- A non-square Vandermonde matrix. -/
def nonsquare [Semiring F] (ι' : ℕ) (α : ι → F) : Matrix ι (Fin ι') F :=
  Matrix.of fun i j => (α i) ^ j.1

lemma nonsquare_mulVecLin [CommSemiring F] {ι' : ℕ} {α₁ : ι ↪ F} {α₂ : Fin ι' → F} {i : ι} :
    (nonsquare ι' α₁).mulVecLin α₂ i = ∑ x, α₂ x * α₁ i ^ x.1 := by
  simp [nonsquare, mulVec_eq_sum]

/-- The transpose of a non-square Vandermonde matrix. -/
def nonsquareTranspose [Field F] (ι' : ℕ) (α : ι ↪ F) : Matrix (Fin ι') ι F :=
  (Vandermonde.nonsquare ι' α)ᵀ

section

variable [CommRing F] {m n : ℕ} {α : Fin m → F}

/-- The maximal upper square submatrix of a Vandermonde matrix is a Vandermonde matrix. -/
lemma subUpFull_of_vandermonde_is_vandermonde (h : n ≤ m) :
    Matrix.vandermonde (α ∘ Fin.castLE h) =
  Matrix.subUpFull (nonsquare n α) (Fin.castLE h) := by
  ext r c
  simp [Matrix.vandermonde, Matrix.subUpFull, nonsquare]

/-- The maximal left square submatrix of a Vandermonde matrix is a Vandermonde matrix. -/
lemma subLeftFull_of_vandermonde_is_vandermonde (h : m ≤ n) :
    Matrix.vandermonde α = Matrix.subLeftFull (nonsquare n α) (Fin.castLE h) := by
  ext r c
  simp [Matrix.vandermonde, Matrix.subLeftFull, nonsquare]

section

variable [IsDomain F]

/-- The rank of a non-square Vandermonde matrix with more rows than columns is the number of
  columns. -/
lemma rank_nonsquare_eq_deg_of_deg_le (inj : Function.Injective α) (h : n ≤ m) :
    (Vandermonde.nonsquare (ι' := n) α).rank = n := by
  suffices ((Vandermonde.nonsquare (ι' := n) α).subUpFull (Fin.castLE h)).rank = n by
    exact Matrix.rank_eq_if_subUpFull_eq h this
  rw[
    ←subUpFull_of_vandermonde_is_vandermonde,
    Matrix.rank_eq_if_det_ne_zero
  ]
  rw [@Matrix.det_vandermonde_ne_zero_iff F _ n _ (α ∘ Fin.castLE h)]
  apply Function.Injective.comp <;> aesop (add simp Fin.castLE_injective)

/-- The rank of a non-square Vandermonde matrix with more columns than rows is the number of rows.
-/
lemma rank_nonsquare_eq_deg_of_ι_le (inj : Function.Injective α) (h : m ≤ n) :
    (Vandermonde.nonsquare (ι' := n) α).rank = m := by
  suffices ((Vandermonde.nonsquare (ι' := n) α).subLeftFull (Fin.castLE h)).rank = m by
    exact Matrix.full_row_rank_via_rank_subLeftFull h this
  rw[
    ←subLeftFull_of_vandermonde_is_vandermonde,
    Matrix.rank_eq_if_det_ne_zero]
  rw[Matrix.det_vandermonde_ne_zero_iff]
  exact inj

@[simp]
lemma rank_nonsquare_rows_eq_min (inj : Function.Injective α) :
    (Vandermonde.nonsquare (ι' := n) α).rank = min m n := by
  by_cases h : m ≤ n
  · rw [rank_nonsquare_eq_deg_of_ι_le inj h]; simp [h]
  · rw [rank_nonsquare_eq_deg_of_deg_le inj] <;> omega

end

theorem mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
    {n : ℕ} [NeZero n] {v : ι ↪ F} {p : F[X]} (h_deg : p.natDegree < n) :
  (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) =
  fun i => p.eval (v i) := by
  ext i
  have hLHS :
      (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) i
        = ∑ x ∈ Finset.range n, (if x < n then p.coeff x * v i ^ x else 0) := by
    simp [nonsquare_mulVecLin, Finset.sum_fin_eq_sum_range, Fin.liftF'_p_coeff]
  have hRHS :
      p.eval (v i) = ∑ x ∈ Finset.range n, p.coeff x * v i ^ x :=
    Polynomial.eval_eq_sum_range' (p := p) (x := v i) (n := n) h_deg
  calc
    (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) i
        = ∑ x ∈ Finset.range n, (if x < n then p.coeff x * v i ^ x else 0) := hLHS
    _ = ∑ x ∈ Finset.range n, p.coeff x * v i ^ x := by
          refine Finset.sum_congr rfl (fun x hx => ?_)
          simp [Finset.mem_range.mp hx]
    _ = p.eval (v i) := by simp [hRHS]

end

end Vandermonde

end

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Data.Fintype.Defs


open Classical
open Polynomial
open Polynomial.Bivariate

namespace Bivariate

noncomputable section

variable {F : Type} [Semiring F]
         (a : F)
         (f g : F[X][Y])

/--
The set of coeffiecients of a bivatiate polynomial.
-/
def coeffs : Finset F[X] := f.support.image (fun n => f.coeff n)

/---
The coeffiecient of `Y^n` is a polynomial in `X`.
-/
def coeff_Y_n (n : ℕ) : F[X] := f.coeff n

/--
The `Y`-degree of a bivariate polynomial.
-/
def degreeY : ℕ := Polynomial.natDegree f

-- Katy: The next def, lemma and def can be deleted. Just keeping for now in case we need
-- the lemma for somethying
def degreesYFinset : Finset ℕ :=
  f.toFinsupp.support

lemma degreesYFinset_nonempty (hf : f ≠ 0) : (degreesYFinset f).Nonempty := by
  rw [degreesYFinset]
  apply Finsupp.support_nonempty_iff.mpr
  intro h
  apply hf
  exact Polynomial.ext (fun n => by rw [← Polynomial.toFinsupp_apply, h]; rfl)


def degreeY' (hf : f ≠ 0) : ℕ :=
  f.toFinsupp.support.max' (degreesYFinset_nonempty f hf)

/--
The polynomial coefficient of the highest power of `Y`. This is the leading coefficient in the
classical sense if the bivariate polynomial is interpreted as a univariate polynomial over `F[X]`.
-/
def leadingCoeffY : F[X] := f.coeff (natDegree f)

/--
The polynomial coeffient of the highest power of `Y` is `0` if and only if the bivariate
polynomial is the zero polynomial.
-/
theorem leadingCoeffY_eq_zero : leadingCoeffY f = 0 ↔ f = 0 :=
  ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (Finset.mem_of_max (degree_eq_natDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

/--
The polynomial coeffient of the highest power of `Y` is not `0` if and only if the
bivariate polynomial is non-zero.
-/
lemma ne_zero_iff_leadingCoeffY_ne_zero : leadingCoeffY f ≠ 0 ↔ f ≠ 0 := by
  rw [Ne, leadingCoeffY_eq_zero f]

/--
Over an intergal domain, the product of two non-zero bivariate polynomials is non-zero.
-/
lemma ne_zero_mul_ne_zero [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0) : f * g ≠ 0 := mul_ne_zero hf hg

/--
Over an integral domain, the `Y`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees.
-/
lemma degreeY_mul [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0)
  : degreeY (f * g) = degreeY f + degreeY g := by
  unfold degreeY
  rw [←ne_zero_iff_leadingCoeffY_ne_zero] at hf
  rw [←ne_zero_iff_leadingCoeffY_ne_zero] at hg
  have h_lc : leadingCoeffY f * leadingCoeffY g ≠ 0 := mul_ne_zero hf hg
  exact Polynomial.natDegree_mul' h_lc

/--
The `X`-degree of a bivariate polynomial.
-/
def degreeX : ℕ := f.toFinsupp.support.sup (fun n => (f.coeff n).natDegree)


/--
The `X`-degree of the product of two non-zero bivariate polynomials is
equal to the sum of their degrees.
-/
lemma degreeX_mul [IsDomain F] (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX (f * g) = degreeX f + degreeX g := by
  unfold degreeX
  sorry

/--
The evaluation at a point of a bivariate polynomial in the first variable `X`.
-/
def evalX : Polynomial F :=
  ⟨Finsupp.mapRange (Polynomial.eval a) eval_zero f.toFinsupp⟩

/--
Evaluating a bivariate polynomial in the first variable `X` on a set of points. This results in
a set of univariate polynomials in `Y`.
-/
def evalSetX (P : Finset F) [Nonempty P]: Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalX a f = h}

/--
The evaluation at a point of a bivariate polynomial in the second variable `Y`.
-/
def evalY : Polynomial F := Polynomial.eval (Polynomial.C a) f

/--
Evaluating a bivariate polynomial in the second variable `Y` on a set of points resulting
in a set of univariate polynomials in `X`.
-/
def evalSetY (P : Finset F) [Nonempty P] : Set (Polynomial F) :=
  {h : Polynomial F | ∃ a ∈ P, evalY a f = h}

/--
The bivariate quotient polynomial.
-/
def quotient : Prop := ∃ q : F[X][Y], g = q * f

/--
The quotient of two non-zero bivariate polynomials is non-zero.
-/
lemma quotient_nezero (q : F[X][Y]) (hg : g ≠ 0) (h_quot_XY : g = q * f)
  : q ≠ 0 := by by_contra h; apply hg; simp [h_quot_XY, h]

/--
A bivariate polynomial is non-zero if and only if all its coefficients are non-zero.
-/
lemma nezero_iff_coeffs_nezero : f ≠ 0 ↔ f.coeff ≠ 0 := by
  apply Iff.intro
  · intro hf
    have f_finsupp : f.toFinsupp ≠ 0 := by aesop
    rw [coeff]
    simp only [ne_eq, Finsupp.coe_eq_zero]
    exact f_finsupp
  · intro f_coeffs
    rw [coeff] at f_coeffs
    aesop

/--
If a non-zero bivariate polynomial `f` divides a non-zero bivariate polynomial `g`, then
all the coefficients of the quoetient are non-zero.
-/
lemma quotient_nezero_iff_coeffs_nezero (q : F[X][Y]) (hg : g ≠ 0)
  (h_quot_XY : g = q * f) : q.coeff ≠ 0 := by
  apply (nezero_iff_coeffs_nezero q).1
  exact quotient_nezero f g q hg h_quot_XY

/--
The `X` degree of the bivarate quotient is bounded above by the difference of the `X`-degrees of
the divisor and divident.
-/
lemma quotient_degX [IsDomain F](q : F[X][Y]) (h_quot_XY : g = q * f) (hf : f ≠ 0) (hg : g ≠ 0) :
  degreeX q ≤ degreeX g - degreeX f := by
  rw [h_quot_XY, degreeX_mul q f]
  · aesop
  · rw [nezero_iff_coeffs_nezero]
    exact quotient_nezero_iff_coeffs_nezero f g q hg h_quot_XY
  · exact hf

/--
The `Y` degree of the bivarate quotient is bounded above by the difference of the `Y`-degrees of
the divisor and divident.
-/
lemma quotient_degY [IsDomain F] (q : F[X][Y]) (h_quot_XY : g = q * f) (hf : f ≠ 0)
  (hg : g ≠ 0) : degreeY q  ≤ degreeY g - degreeY f := by
  rw [h_quot_XY, degreeY_mul q f]
  · aesop
  · rw [nezero_iff_coeffs_nezero q]
    exact quotient_nezero_iff_coeffs_nezero f g q hg h_quot_XY
  · exact hf

def monomial_y (n : ℕ) : F[X] →ₗ[F[X]] F[X][Y] where
  toFun t := ⟨Finsupp.single n t⟩
  map_add' x y := by rw [Finsupp.single_add]; aesop
  map_smul' r x := by simp; rw[smul_monomial]; aesop


def monomial_xy (n m : ℕ) : F →ₗ[F] F[X][Y] where
  toFun t := ⟨Finsupp.single m ⟨(Finsupp.single n t)⟩⟩
  map_add' x y := by
    simp only [ofFinsupp_single, Polynomial.monomial_add, Polynomial.monomial_add]
  map_smul' x y := by
    simp only [smul_eq_mul, ofFinsupp_single, RingHom.id_apply]
    rw[smul_monomial, smul_monomial]
    simp

theorem monomial_xy_def (m n : ℕ) (c : F) : monomial_xy n m c = monomial m (monomial n c) := by
  unfold monomial_xy
  simp

theorem monomial_xy_add (n m : ℕ) (r s : F) :
  monomial_xy n m (r + s) = monomial_xy n m r + monomial_xy n m s :=
  (monomial_xy n m).map_add _ _

theorem monomial_xy_mul_monomial_xy (n m p q : ℕ) (r s : F) :
    monomial_xy n m r * monomial_xy p q s = monomial_xy (n + p) (m + q) (r * s) :=
  toFinsupp_injective <| by
  unfold monomial_xy
  rw [@toFinsupp_mul, @AddMonoidAlgebra.mul_def]
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, toFinsupp_monomial, mul_zero,
    Finsupp.single_zero, Finsupp.sum_single_index, zero_mul]
  rw [@monomial_mul_monomial]


@[simp]
theorem monomial_pow (n m k : ℕ) (r : F) :
  monomial_xy n m r ^ k = monomial_xy (n * k) (m * k) (r ^ k) := by
  unfold monomial_xy
  simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.monomial_pow]


theorem smul_monomial_xy {S} [SMulZeroClass S F] (a : S) (n m : ℕ) (b : F) :
    a • monomial_xy n m b = monomial_xy n m (a • b) := by
    rw [monomial_xy]
    simp only [ofFinsupp_single, LinearMap.coe_mk, AddHom.coe_mk]
    rw [@Polynomial.smul_monomial, @Polynomial.smul_monomial]


@[simp]
theorem monomial_xy_eq_zero_iff (t : F) (n m : ℕ) : monomial_xy n m t = 0 ↔ t = 0 := by
  rw [monomial_xy]
  simp

theorem monomial_xy_eq_monomial_xy_iff {m n p q : ℕ} {a b : F} :
    monomial_xy n m a = monomial_xy p q b ↔ n = p ∧ m = q ∧ a = b ∨ a = 0 ∧ b = 0 := by
    unfold monomial_xy
    simp
    rw [@monomial_eq_monomial_iff, @monomial_eq_monomial_iff]
    aesop

def totalDegree (f : F[X][Y]) : ℕ :=
  f.support.sup (fun m => m + (f.coeff m).natDegree)

lemma monomial_xy_degree (n m : ℕ) (a : F) (ha : a ≠ 0) :
  totalDegree (monomial_xy n m a) = n + m := by
  unfold totalDegree
  rw
    [
      monomial_xy_def,
      Polynomial.support_monomial,
      Finset.sup_singleton,
      Nat.add_comm
    ] <;> simp [ha]


theorem totalDegree_prod (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  unfold totalDegree
  rw [@mul_eq_sum_sum]
  sorry


end
end Bivariate

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.FiniteAlgebraGrowth
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.PolynomialGrowthAffine

/-!
# Hilbert-polynomial degree under finite injective affine algebra maps
-/

@[expose] public section

noncomputable section

open Filter

namespace AffineHilbert

/-- A finite injective map between affine coordinate algebras preserves the degree
of their canonical total-degree Hilbert polynomials. -/
theorem hilbertPolynomial_natDegree_eq_of_finite_injective_algebraMap
    {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]
    {I : Ideal (MvPolynomial σ F)} {J : Ideal (MvPolynomial τ F)}
    [Algebra (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    [IsScalarTower F (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    [Module.Finite (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    (hI : I ≠ ⊤)
    (hg : Function.Injective
      (algebraMap (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I))) :
    (hilbertPolynomial I).natDegree = (hilbertPolynomial J).natDegree := by
  let B := MvPolynomial τ F ⧸ J
  let A := MvPolynomial σ F ⧸ I
  have hJ : J ≠ ⊤ := by
    intro hJ
    have hzerooneB : (0 : B) = 1 := by
      exact (Ideal.Quotient.subsingleton_iff.mpr hJ).elim _ _
    have hzerooneA : (0 : A) = 1 := by
      rw [← map_zero (algebraMap B A), ← map_one (algebraMap B A), hzerooneB]
    have hsubA : Subsingleton A := subsingleton_iff_zero_eq_one.mp hzerooneA
    exact hI (Ideal.Quotient.subsingleton_iff.mp hsubA)
  apply Nat.le_antisymm
  · obtain ⟨c, hc, m, hm, hbound⟩ := hilbertFunction_le_mul_rescaled_of_finite
      (F := F) (I := I) (J := J)
    apply natDegree_le_of_eventually_eval_nat_le_mul_affine
      (hilbertPolynomial_ne_zero hI) (m := m) (c := c) (d := c) hm hc
    · filter_upwards [hilbertPolynomial_eventually_eval I] with N hN
      rw [hN]
      positivity
    · obtain ⟨TI, hIev⟩ := hilbertPolynomial_eventually I
      obtain ⟨TJ, hJev⟩ := hilbertPolynomial_eventually J
      filter_upwards [Filter.eventually_ge_atTop (max TI TJ)] with N hN
      rw [hIev N ((le_max_left TI TJ).trans hN),
        hJev (c * N + c) ((le_max_right TI TJ).trans hN |>.trans
          ((Nat.le_mul_of_pos_left N hc).trans (Nat.le_add_right _ _)))]
      have hb : hilbertFunction I N ≤ m * hilbertFunction J (c * N + c) := by
        simpa [Nat.mul_add] using hbound N
      exact_mod_cast hb
  · obtain ⟨c, hc, hbound⟩ := hilbertFunction_le_rescaled_of_injective_algHom
      (IsScalarTower.toAlgHom F B A) hg
    apply natDegree_le_of_eventually_eval_nat_le_mul_affine
      (hilbertPolynomial_ne_zero hJ) (m := 1) (c := c) (d := 0) Nat.zero_lt_one hc
    · filter_upwards [hilbertPolynomial_eventually_eval J] with N hN
      rw [hN]
      positivity
    · obtain ⟨TI, hIev⟩ := hilbertPolynomial_eventually I
      obtain ⟨TJ, hJev⟩ := hilbertPolynomial_eventually J
      filter_upwards [Filter.eventually_ge_atTop (max TI TJ)] with N hN
      rw [hJev N ((le_max_right TI TJ).trans hN),
        hIev (c * N + 0) ((le_max_left TI TJ).trans hN |>.trans (by
          simpa using Nat.le_mul_of_pos_left N hc))]
      simpa using (show (hilbertFunction J N : ℚ) ≤
        hilbertFunction I (c * N) by exact_mod_cast hbound N)

/-- AlgHom-form wrapper for the finite injective extension theorem. -/
theorem hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
    {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]
    {I : Ideal (MvPolynomial σ F)} {J : Ideal (MvPolynomial τ F)}
    (g : (MvPolynomial τ F ⧸ J) →ₐ[F] (MvPolynomial σ F ⧸ I))
    (hg : Function.Injective g) (hI : I ≠ ⊤)
    (hfinite : let _ : Algebra (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I) :=
        g.toRingHom.toAlgebra
      Module.Finite (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)) :
    (hilbertPolynomial I).natDegree = (hilbertPolynomial J).natDegree := by
  let _ : Algebra (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I) :=
    g.toRingHom.toAlgebra
  let _ : IsScalarTower F (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I) :=
    IsScalarTower.of_algHom g
  let _ : Module.Finite (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I) := hfinite
  apply hilbertPolynomial_natDegree_eq_of_finite_injective_algebraMap hI
  change Function.Injective g
  exact hg

end AffineHilbert

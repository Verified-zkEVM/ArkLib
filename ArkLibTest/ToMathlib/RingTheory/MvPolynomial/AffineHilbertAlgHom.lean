/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom

/-!
# Acceptance tests for affine Hilbert polynomials under algebra maps

The examples use the inclusion `ℚ[x₀] → ℚ[x₀, x₁]` induced by `rename Fin.castSucc` and the
quotient maps `ℚ[x₀] → ℚ[x₀] ⧸ I`. The inclusion is injective and sends variables to degree `1`,
which gives `H(⊥, N) ≤ H(⊥, N)` across one and two variables, computed at `N = 3` as `4 ≤ 10`.
Since the natural degrees are `1 < 2`, the finite-map comparison shows that the inclusion is not
finite, so injectivity alone does not give equality of degrees. The quotient map to the zero ring
is finite and surjective with degrees `0 < 1`, so injectivity is needed for equality. A quotient
map recovers the comparison along inclusions of ideals, and the source-shaped statements
(`Algebra` instance with `Module.Finite`, the `c * (N + 1)` bound, the surjective form with
`I ≠ ⊤`) are derived from the general ones.
-/

open MvPolynomial Filter

namespace AffineHilbertAlgHomTest

/-- The inclusion `ℚ[x₀] ⧸ ⊥ → ℚ[x₀, x₁] ⧸ ⊥` induced by `rename Fin.castSucc`. -/
noncomputable def incl : (MvPolynomial (Fin 1) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) →ₐ[ℚ]
    (MvPolynomial (Fin 2) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))) :=
  Ideal.quotientMapₐ ⊥ (rename Fin.castSucc) bot_le

theorem incl_injective : Function.Injective incl :=
  Ideal.quotientMap_injective' (H := bot_le) fun p hp ↦ by
    have hp' : rename Fin.castSucc p = 0 := by simpa using hp
    exact (Submodule.mem_bot _).mpr
      (rename_injective _ (Fin.castSucc_injective 1) (hp'.trans (map_zero _).symm))

theorem incl_X_mem (i : Fin 1) :
    incl (Ideal.Quotient.mk ⊥ (X i)) ∈ quotientDegreeLE (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) 1 := by
  change Ideal.Quotient.mk ⊥ (rename Fin.castSucc (X i)) ∈ _
  rw [rename_X]
  exact mk_X_mem_quotientDegreeLE _ _

/-- The injective bound with the explicit constant `c = 1`, evaluated at `N = 3`: the four
monomials of degree at most `3` in one variable embed among the ten in two variables. -/
example : affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 3 ≤
    affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 * 3) :=
  affineHilbertFunction_le_of_injective incl incl_injective incl_X_mem 3

example : affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 3 = 4 ∧
    affineHilbertFunction (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) 3 = 10 := by
  simp [affineHilbertFunction_bot, Nat.choose]

/-- The injective degree comparison for the inclusion reads `1 ≤ 2`. -/
example : (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree = 1 ∧
    (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 2) ℚ))).natDegree = 2 :=
  ⟨by simp [natDegree_affineHilbertPolynomial_bot],
    by simp [natDegree_affineHilbertPolynomial_bot]⟩

/-- Finiteness is needed in `natDegree_affineHilbertPolynomial_le_of_finite` and in the equality:
the inclusion is injective, and if it were finite the plane would have Hilbert-polynomial degree
at most that of the line. -/
example : ¬incl.Finite := fun hfin ↦ by
  have h := natDegree_affineHilbertPolynomial_le_of_finite incl hfin
  simp [natDegree_affineHilbertPolynomial_bot] at h

/-- Injectivity is needed in the equality: the quotient map `ℚ[x₀] → ℚ[x₀] ⧸ ⊤` is finite (being
surjective), but the degrees are `0` and `1`. -/
example :
    let g := Ideal.Quotient.factorₐ ℚ (bot_le : (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ≤ ⊤)
    g.Finite ∧ ¬Function.Injective g ∧
      (affineHilbertPolynomial (⊤ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree ≠
        (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree := by
  intro g
  refine ⟨AlgHom.Finite.of_surjective g (Ideal.Quotient.factor_surjective bot_le),
    fun hinj ↦ ?_, ?_⟩
  · have : Nontrivial (MvPolynomial (Fin 1) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) :=
      Ideal.Quotient.nontrivial_iff.mpr bot_ne_top
    exact one_ne_zero (hinj (Subsingleton.elim _ _))
  · simp [natDegree_affineHilbertPolynomial_bot]

/-- A quotient map `MvPolynomial σ k ⧸ I → MvPolynomial σ k ⧸ J` for `I ≤ J` is surjective, which
recovers `natDegree_affineHilbertPolynomial_le_of_le`. -/
example {k σ : Type*} [Field k] [Finite σ] {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J) :
    (affineHilbertPolynomial J).natDegree ≤ (affineHilbertPolynomial I).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_surjective (Ideal.Quotient.factorₐ k hIJ)
    (Ideal.Quotient.factor_surjective hIJ)

variable {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]
  {I : Ideal (MvPolynomial σ F)} {J : Ideal (MvPolynomial τ F)}

/-- The source's finite bound `H(I, N) ≤ m * H(J, c * (N + 1))`, from the sharper `c * N` form and
monotonicity. -/
example [Algebra (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    [IsScalarTower F (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    [Module.Finite (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)] :
    ∃ c > 0, ∃ m > 0, ∀ N,
      affineHilbertFunction I N ≤ m * affineHilbertFunction J (c * (N + 1)) := by
  obtain ⟨m, c, hm, hc, h⟩ := exists_affineHilbertFunction_le_mul_of_finite
    (IsScalarTower.toAlgHom F (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I))
    (RingHom.finite_algebraMap.mpr inferInstance)
  exact ⟨c, hc, m, hm, fun N ↦ (h N).trans (Nat.mul_le_mul_left m
    (affineHilbertFunction_mono J (Nat.mul_le_mul_left c (Nat.le_succ N))))⟩

/-- The source's equality for a finite injective `algebraMap`, with its hypothesis `I ≠ ⊤`. -/
example [Algebra (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    [IsScalarTower F (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    [Module.Finite (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)] (_hI : I ≠ ⊤)
    (hg : Function.Injective (algebraMap (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I))) :
    (affineHilbertPolynomial I).natDegree = (affineHilbertPolynomial J).natDegree :=
  natDegree_affineHilbertPolynomial_eq_of_finite_of_injective
    (IsScalarTower.toAlgHom F (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I))
    (RingHom.finite_algebraMap.mpr inferInstance) hg

/-- The source's surjective comparison, with its hypothesis `I ≠ ⊤`. -/
example (g : (MvPolynomial τ F ⧸ J) →ₐ[F] (MvPolynomial σ F ⧸ I)) (hg : Function.Surjective g)
    (_hI : I ≠ ⊤) :
    (affineHilbertPolynomial I).natDegree ≤ (affineHilbertPolynomial J).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_surjective g hg

/-- The source's injective comparison, with its hypothesis `J ≠ ⊤`. -/
example (g : (MvPolynomial τ F ⧸ J) →ₐ[F] (MvPolynomial σ F ⧸ I)) (hg : Function.Injective g)
    (_hJ : J ≠ ⊤) :
    (affineHilbertPolynomial J).natDegree ≤ (affineHilbertPolynomial I).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_injective g hg

end AffineHilbertAlgHomTest

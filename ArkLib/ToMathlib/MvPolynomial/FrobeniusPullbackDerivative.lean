/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Coordinate degrees and derivatives under the inverse Frobenius twist

Mapping multivariate coefficients through a ring equivalence preserves the monomial support.
Consequently it preserves every coordinate degree exactly and commutes with each partial
derivative.  This file specializes those facts to the inverse Frobenius coefficient twist.

No contraction, geometric reconstruction, or agreement bound is proved here.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

section CoefficientEquiv

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

/-- A coefficient ring equivalence preserves every coordinate degree exactly. -/
theorem degreeOf_map_ringEquiv (f : R ≃+* S) (G : MvPolynomial σ R) (i : σ) :
    degreeOf i (map f.toRingHom G) = degreeOf i G := by
  classical
  simp only [degreeOf_def, degrees_map_of_injective G (f := f.toRingHom) f.injective]

/-- Partial differentiation commutes with a coefficient ring equivalence. -/
theorem pderiv_map_ringEquiv (f : R ≃+* S) (G : MvPolynomial σ R) (i : σ) :
    pderiv i (map f.toRingHom G) = map f.toRingHom (pderiv i G) :=
  pderiv_map

/-- A coefficient ring equivalence preserves nonvanishing of every partial derivative. -/
theorem pderiv_map_ringEquiv_ne_zero_iff (f : R ≃+* S) (G : MvPolynomial σ R) (i : σ) :
    pderiv i (map f.toRingHom G) ≠ 0 ↔ pderiv i G ≠ 0 := by
  rw [pderiv_map_ringEquiv]
  constructor
  · intro hmap hzero
    exact hmap (by rw [hzero, map_zero])
  · intro h hmap
    apply h
    apply map_injective f.toRingHom f.injective
    simpa using hmap

end CoefficientEquiv

variable {K σ : Type*} [Field K] (p e : ℕ) [ExpChar K p] [PerfectField K]

/-- The inverse Frobenius coefficient twist preserves every coordinate degree exactly. -/
theorem degreeOf_inverseFrobeniusTwist (G : MvPolynomial σ K) (i : σ) :
    degreeOf i (inverseFrobeniusTwist p e G) = degreeOf i G :=
  degreeOf_map_ringEquiv (iterateFrobeniusEquiv K p e).symm G i

/-- The inverse Frobenius coefficient twist commutes with every partial derivative. -/
theorem pderiv_inverseFrobeniusTwist (G : MvPolynomial σ K) (i : σ) :
    pderiv i (inverseFrobeniusTwist p e G) =
      inverseFrobeniusTwist p e (pderiv i G) :=
  pderiv_map

/-- A partial derivative is nonzero exactly when the corresponding derivative after inverse
Frobenius coefficient twist is nonzero. -/
theorem pderiv_inverseFrobeniusTwist_ne_zero_iff (G : MvPolynomial σ K) (i : σ) :
    pderiv i (inverseFrobeniusTwist p e G) ≠ 0 ↔ pderiv i G ≠ 0 :=
  pderiv_map_ringEquiv_ne_zero_iff (iterateFrobeniusEquiv K p e).symm G i

/-- Forward form used after choosing a root coordinate with nonzero partial derivative. -/
theorem pderiv_inverseFrobeniusTwist_ne_zero {G : MvPolynomial σ K} {i : σ}
    (hG : pderiv i G ≠ 0) : pderiv i (inverseFrobeniusTwist p e G) ≠ 0 :=
  (pderiv_inverseFrobeniusTwist_ne_zero_iff p e G i).mpr hG

/-- A coefficient-sensitive characteristic-two canary.  For a root of `a ^ 3 + a + 1`, the
twist sends the coefficient of `X 0` to `a ^ 2 + a`; differentiation exposes that coefficient,
which is nonzero. -/
theorem pderiv_inverseFrobeniusTwist_cubicCoefficient_canary
    {L : Type*} [Field L] [CharP L 2] [PerfectField L] (a : L)
    (ha : a ^ 3 + a + 1 = 0) :
    pderiv 0 (inverseFrobeniusTwist 2 1
      (C a * X 0 + X 1 : MvPolynomial (Fin 2) L)) = C (a ^ 2 + a) ∧
      pderiv 0 (inverseFrobeniusTwist 2 1
        (C a * X 0 + X 1 : MvPolynomial (Fin 2) L)) ≠ 0 := by
  obtain ⟨htwist, _⟩ := inverseFrobeniusTwist_cubicCoefficient_canary a ha
  have ha0 : a ≠ 0 := by
    intro hzero
    rw [hzero] at ha
    simp at ha
  have hcoeff0 : a ^ 2 + a ≠ 0 := by
    intro hzero
    have hmul : a * (a + 1) = 0 := by
      simpa only [mul_add, mul_one, pow_two] using hzero
    have hadd : a + 1 = 0 := (mul_eq_zero.mp hmul).resolve_left ha0
    have ha1 : a = 1 := by
      simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using
        congrArg (fun x : L ↦ x + 1) hadd
    rw [ha1] at ha
    exact one_ne_zero (by
      simpa only [one_pow, CharTwo.add_self_eq_zero, zero_add] using ha)
  have hder :
      pderiv 0 (inverseFrobeniusTwist 2 1
        (C a * X 0 + X 1 : MvPolynomial (Fin 2) L)) = C (a ^ 2 + a) := by
    rw [htwist]
    simp
  refine ⟨hder, ?_⟩
  rw [hder]
  exact C_ne_zero.mpr hcoeff0

end

end MvPolynomial

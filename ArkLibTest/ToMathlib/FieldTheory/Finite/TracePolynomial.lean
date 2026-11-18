/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToMathlib.FieldTheory.Finite.TracePolynomial
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for trace polynomials and trace coordinates -/

open FiniteField Polynomial

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem finrank_eq : Module.finrank (ZMod 2) (GaloisField 2 2) = 2 :=
  GaloisField.finrank 2 (by norm_num)

private noncomputable def b : Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) :=
  Module.finBasisOfFinrankEq _ _ finrank_eq

-- Over `F₂ ⊆ F₄`, the trace polynomial `X + X²` of `1` has degree `q₀ᵏ⁻¹ = 2¹ = 2`.
example : (tracePolynomial (ZMod 2) (1 : GaloisField 2 2)).natDegree = 2 := by
  rw [natDegree_tracePolynomial one_ne_zero, finrank_eq, ZMod.card]
  norm_num

-- The trace polynomial of `0` is zero, so the degree bound is not an equality there.
example : tracePolynomial (ZMod 2) (0 : GaloisField 2 2) = 0 := by
  simp [tracePolynomial, finrank_eq]

-- `T₁(1) = Tr(1) = [F₄ : F₂] = 2 = 0` in `F₂`.
example : (tracePolynomial (ZMod 2) (1 : GaloisField 2 2)).eval 1 = 0 := by
  rw [eval_tracePolynomial, mul_one, ← map_one (algebraMap (ZMod 2) (GaloisField 2 2)),
    Algebra.trace_algebraMap, finrank_eq]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  rw [show (2 : ZMod 2) = 0 from rfl, map_zero]

-- A basis of `F₄` over `F₂` gives the bijection `x ↦ (Tr(b₀ x), Tr(b₁ x))` onto `F₂²`.
example : Function.Bijective (traceCoordinateMap (ZMod 2) b) :=
  traceCoordinateMap_bijective b

-- Two elements of `F₄` with equal trace coordinates are equal.
example (x y : GaloisField 2 2)
    (h : ∀ i, Algebra.trace (ZMod 2) _ (b i * x) = Algebra.trace (ZMod 2) _ (b i * y)) :
    x = y :=
  (traceCoordinateEquiv (ZMod 2) b).injective (funext h)

/-- info: 'FiniteField.eval_tracePolynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.eval_tracePolynomial

/-- info: 'FiniteField.natDegree_tracePolynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.natDegree_tracePolynomial

/-- info: 'FiniteField.traceCoordinateMap_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.traceCoordinateMap_bijective

/-- info: 'FiniteField.exists_bijective_traceCoordinateMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.exists_bijective_traceCoordinateMap

/-- info: 'FiniteField.coeff_tracePolynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.coeff_tracePolynomial

/-- info: 'FiniteField.natDegree_tracePolynomial_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.natDegree_tracePolynomial_le

/-- info: 'FiniteField.traceCoordinateMap_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.traceCoordinateMap_apply

/-- info: 'FiniteField.traceCoordinateEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.traceCoordinateEquiv_apply

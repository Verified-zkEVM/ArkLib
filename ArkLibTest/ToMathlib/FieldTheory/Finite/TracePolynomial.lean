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
example : Function.Bijective (traceCoordinateEquiv (ZMod 2) b) :=
  (traceCoordinateEquiv (ZMod 2) b).bijective

-- Two elements of `F₄` with equal trace coordinates are equal.
example (x y : GaloisField 2 2)
    (h : ∀ i, Algebra.trace (ZMod 2) _ (b i * x) = Algebra.trace (ZMod 2) _ (b i * y)) :
    x = y := by
  apply (traceCoordinateEquiv (ZMod 2) b).injective
  funext i
  simpa only [traceCoordinateEquiv_apply] using h i

-- `T_c` is additive in `c`: `T_{1 + b₀} = T_1 + T_{b₀}` in `F₄[X]`.
example : tracePolynomial (ZMod 2) (1 + b 0) =
    tracePolynomial (ZMod 2) 1 + tracePolynomial (ZMod 2) (b 0) :=
  tracePolynomial_add 1 (b 0)

-- `T_c` is additive as a function, here on `F₄` itself.
example (c x y : GaloisField 2 2) :
    (tracePolynomial (ZMod 2) c).eval (x + y) =
      (tracePolynomial (ZMod 2) c).eval x + (tracePolynomial (ZMod 2) c).eval y :=
  eval_tracePolynomial_add c x y

-- It is also additive on the `F₄`-algebra `F₄[Y]`, where it is a linearized polynomial.
example (c : GaloisField 2 2) (x y : Polynomial (GaloisField 2 2)) :
    aeval (x + y) (tracePolynomial (ZMod 2) c) =
      aeval x (tracePolynomial (ZMod 2) c) + aeval y (tracePolynomial (ZMod 2) c) :=
  aeval_tracePolynomial_add c x y

-- Squaring is additive in characteristic two: `(x + y)² = x² + y²`, the case `j = 1`.
example (x y : GaloisField 2 2) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  simpa [ZMod.card] using add_pow_card_pow (ZMod 2) x y 1

-- `ψ` maps the trace-dual basis `b*` of `b` to the standard basis of `F₂²`:
-- `Tr(bᵢ b*ⱼ) = δᵢⱼ`.
example (j : Fin 2) :
    traceCoordinateEquiv (ZMod 2) b
        ((Algebra.traceForm (ZMod 2) (GaloisField 2 2)).dualBasis
          (traceForm_nondegenerate _ _) b j) = Pi.single j 1 := by
  funext i
  rw [traceCoordinateEquiv_apply, ← Algebra.traceForm_apply,
    LinearMap.BilinForm.apply_dualBasis_right _ (Algebra.traceForm_isSymm _)]
  simp [Pi.single_apply]

/-- info: 'FiniteField.eval_tracePolynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.eval_tracePolynomial

/-- info: 'FiniteField.natDegree_tracePolynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.natDegree_tracePolynomial

/-- info: 'FiniteField.coeff_tracePolynomial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.coeff_tracePolynomial

/-- info: 'FiniteField.natDegree_tracePolynomial_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.natDegree_tracePolynomial_le

/-- info: 'FiniteField.traceCoordinateEquiv_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.traceCoordinateEquiv_apply

/-- info: 'FiniteField.add_pow_card_pow' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.add_pow_card_pow

/-- info: 'FiniteField.tracePolynomial_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.tracePolynomial_add

/-- info: 'FiniteField.aeval_tracePolynomial_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.aeval_tracePolynomial_add

/-- info: 'FiniteField.eval_tracePolynomial_add' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FiniteField.eval_tracePolynomial_add

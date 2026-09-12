/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.PerturbationCoefficient
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Degree-one system-to-perturbation construction

This bounded producer implements the degree-one Sylvester resultant in Rojas's
construction: the input is `a*x+b`, the fixed perturbing system is `x-1`, and
its specialized auxiliary form is `t+u*x`. The outer stored variable is `s`
and the inner variable is `t`. Its determinant is computed from the input
coefficients, without supplying roots or a resultant. This is only the
one-equation, degree-one slice; it is not a general isolated-root solver.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.Linear

open CompPoly CompPoly.CPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F] [BEq F] [LawfulBEq F]

/-- Stored original equation of the supported family. -/
def equation (a b : F) : CPolynomial F := C a * X + C b

/-- The stored input has precisely the advertised equation semantics. -/
theorem equation_eval (a b x : F) :
    (equation a b).toPoly.eval x = a * x + b := by
  simp [equation, toPoly_add, toPoly_mul, C_toPoly, X_toPoly]

/-- The computed Sylvester determinant of `a*x+b-s*(x-1)` and `t+u*x`.
Both allowed supports are `{0,1}`, so zero-coordinate affine roots are retained. -/
def characteristic (a b u : F) : CPolynomial (CPolynomial F) :=
  (C (C a) - X) * C X - (C (C b) + X) * C (C u)

/-- The coefficient at `s=0`, computed from the stored characteristic polynomial. -/
def perturbation (a b u : F) : CPolynomial F :=
  (characteristic a b u).coeff 0

/-- The producer's explicit system-dependent characteristic identity. -/
theorem characteristic_identity (a b u : F) :
    characteristic a b u =
      C (C a * X - C b * C u) - X * C (X + C u) := by
  simp only [characteristic, ← CHom_apply, map_sub, map_mul, map_add]
  ring

/-- Coefficient extraction yields the expected linear eliminant. -/
theorem perturbation_eq (a b u : F) :
    perturbation a b u = C a * X - C (b * u) := by
  rw [perturbation, characteristic_identity]
  simp only [coeff_sub, coeff_C, ↓reduceIte, coeff_X_mul_zero, sub_zero]
  rw [← CHom_apply b, ← CHom_apply u, ← map_mul]
  rfl

omit [Nontrivial F] [BEq F] [LawfulBEq F] in
/-- This is the actual padded degree-one resultant, including degenerations. -/
theorem resultant_linear (a b c d : F) :
    Polynomial.resultant (Polynomial.C a * Polynomial.X + Polynomial.C b)
      (Polynomial.C c * Polynomial.X + Polynomial.C d) 1 1 = a * d - b * c := by
  simp only [Polynomial.resultant, Nat.reduceAdd, Polynomial.sylvester, Fin.val_eq_zero,
    zero_add, Set.mem_Icc, zero_le, true_and, tsub_zero, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Matrix.det_fin_two, Fin.isValue, Matrix.of_apply,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte, Polynomial.coeff_X_zero,
    MulZeroClass.mul_zero, Polynomial.coeff_C_zero, Nat.mod_succ, Std.le_refl,
    Polynomial.coeff_X_one, mul_one, Polynomial.coeff_C_succ, add_zero]
  change d * a - b * c = _
  ring

/-- The determinant construction agrees with the resultant of the perturbed input. -/
theorem characteristic_resultant (a b u : F) :
    characteristic a b u =
      Polynomial.resultant
        (Polynomial.C (C (C a) - X) * Polynomial.X + Polynomial.C (C (C b) + X))
        (Polynomial.C (C (C u)) * Polynomial.X + Polynomial.C (C (X : CPolynomial F))) 1 1 := by
  rw [resultant_linear]
  rfl

/-- Whenever the constant perturbation coefficient is nonzero, the existing
lowest-coefficient scanner returns precisely this computed eliminant. -/
theorem extract_eq (a b u : F) (h : perturbation a b u ≠ 0) :
    toricPerturbationCoefficient? (characteristic a b u) = some (perturbation a b u) := by
  apply toricPerturbationCoefficient?_eq_some_iff.mpr
  refine ⟨h, 0, ?_, rfl, by omega⟩
  by_contra hn
  exact h (coeff_eq_zero_of_size_le _ (by omega))

/-- Nonzero leading input coefficient makes the extracted eliminant nonzero,
for every auxiliary specialization, even when the input root is zero. -/
theorem perturbation_ne_zero (a b u : F) (ha : a ≠ 0) :
    perturbation a b u ≠ 0 := by
  intro hz
  have h := congrArg (fun p : CPolynomial F ↦ p.toPoly.coeff 1) hz
  rw [perturbation_eq] at h
  exact ha (by simpa [toPoly_sub, toPoly_mul, C_toPoly, X_toPoly, toPoly_zero] using h)

/-- Unconditional extraction on the supported nonconstant family. -/
theorem extract_of_leading_ne_zero (a b u : F) (ha : a ≠ 0) :
    toricPerturbationCoefficient? (characteristic a b u) = some (perturbation a b u) :=
  extract_eq a b u (perturbation_ne_zero a b u ha)

/-- Any root of the original input supplies a factor of the computed eliminant;
no nonzero-coordinate hypothesis occurs. -/
theorem factor_of_root (a b u x : F) (hx : a * x + b = 0) :
    perturbation a b u = C a * (X + C (u * x)) := by
  rw [perturbation_eq]
  have hb : b = -(a * x) := eq_neg_of_add_eq_zero_right hx
  rw [hb]
  simp only [← CHom_apply, map_neg, map_mul]
  ring

end ArkLib.Rojas.Producer.Linear

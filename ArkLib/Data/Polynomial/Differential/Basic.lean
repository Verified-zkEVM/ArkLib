/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Kai Zhe Zheng
-/
module

public import ArkLib.Data.Polynomial.Differential.Types
public import ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

/-!
# Specialization and evaluation of finite-jet polynomial relations

This file defines two ways to interpret a polynomial relation in `X, Y₀, ..., Y_d`:

* `differentialSpecializationHom` substitutes a polynomial and its Hasse derivatives for the
  formal jet variables;
* `jetEvaluation` evaluates the formal variables at one scalar point and one scalar jet.

The comparison theorem `eval_differentialSpecialization` says that these interpretations agree
after evaluating the specialized univariate polynomial. No characteristic hypothesis is needed:
specialization uses Hasse derivatives and is valid over every commutative semiring. The scalar
Hasse jet is also compatible with affine combinations of polynomials.

## Main statements

* `eval_differentialSpecialization`: evaluation of a differential specialization on the Hasse
  jet.
* `polynomialJet_affine_combination`: affine combinations commute with taking a Hasse jet.

## References
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F : Type*} {d : ℕ}

/-- Substitute `X`, a polynomial `P`, and its Hasse derivatives into a differential polynomial. -/
def differentialSpecializationHom [CommSemiring F] (P : F[X]) :
    DifferentialPolynomial F d →ₐ[F] F[X] :=
  MvPolynomial.aeval fun v : JetVariable d ↦ match v with
    | none => Polynomial.X
    | some j => Polynomial.hasseDeriv j P

/-- Apply `differentialSpecializationHom` to a differential polynomial. -/
def differentialSpecialization [CommSemiring F] (Q : DifferentialPolynomial F d) (P : F[X]) :
    F[X] :=
  differentialSpecializationHom P Q

/-- `differentialSpecializationHom P Q` is `differentialSpecialization Q P`. -/
@[simp]
theorem differentialSpecializationHom_apply [CommSemiring F]
    (Q : DifferentialPolynomial F d) (P : F[X]) :
    differentialSpecializationHom P Q = differentialSpecialization Q P :=
  rfl

/-- Specialization sends the constant `C a` to `Polynomial.C a`. -/
@[simp]
theorem differentialSpecialization_C [CommSemiring F] (a : F) (P : F[X]) :
    differentialSpecialization (d := d) (MvPolynomial.C a) P = Polynomial.C a := by
  simp [differentialSpecialization, differentialSpecializationHom]

/-- Specialization sends the distinguished variable `X none` to `Polynomial.X`. -/
@[simp]
theorem differentialSpecialization_x [CommSemiring F] (P : F[X]) :
    differentialSpecialization (d := d) (MvPolynomial.X none) P = Polynomial.X := by
  simp [differentialSpecialization, differentialSpecializationHom]

/-- Specialization at `P` sends the jet variable `Y_j` to the Hasse derivative
`hasseDeriv j P`. -/
@[simp]
theorem differentialSpecialization_jet [CommSemiring F] (j : Fin (d + 1)) (P : F[X]) :
    differentialSpecialization (MvPolynomial.X (some j)) P = Polynomial.hasseDeriv j P := by
  simp [differentialSpecialization, differentialSpecializationHom]

/-- Evaluate a differential polynomial at a base point and a formal Hasse jet. -/
def jetEvaluation [CommSemiring F] (Q : DifferentialPolynomial F d) (a : F)
    (jet : Fin (d + 1) → F) : F :=
  MvPolynomial.eval (fun v ↦ match v with
    | none => a
    | some j => jet j) Q

/-- The scalar Hasse jet of `P` at `a`, through order `d`. -/
def polynomialJet [Semiring F] (a : F) (P : F[X]) : Fin (d + 1) → F :=
  Polynomial.hasseJet (d + 1) a P

/-- The Hasse jet of an affine combination is the affine combination of the Hasse jets. -/
theorem polynomialJet_affine_combination [Semiring F] (center z : F) (P Q : F[X]) :
    polynomialJet (d := d) center (P + Polynomial.C z * Q) =
      fun j ↦ polynomialJet center P j + z * polynomialJet center Q j := by
  rw [← Polynomial.smul_eq_C_mul]
  funext j
  simp [polynomialJet]

/-- Evaluating a differential specialization at `a` is evaluation on the Hasse jet of `P` at
`a`. -/
theorem eval_differentialSpecialization [CommSemiring F] (Q : DifferentialPolynomial F d)
    (P : F[X]) (a : F) :
    (differentialSpecialization Q P).eval a = jetEvaluation Q a (polynomialJet a P) := by
  rw [differentialSpecialization, differentialSpecializationHom, jetEvaluation]
  change Polynomial.evalRingHom a
      (MvPolynomial.eval₂Hom Polynomial.C
        (fun v ↦ match v with
          | none => Polynomial.X
          | some j => Polynomial.hasseDeriv j P) Q) = _
  rw [MvPolynomial.map_eval₂Hom]
  change MvPolynomial.eval₂Hom _ _ Q = MvPolynomial.eval₂Hom (RingHom.id F) _ Q
  apply MvPolynomial.eval₂Hom_congr
  · ext x
    simp
  · funext v
    cases v with
    | none => simp
    | some j => rfl
  · rfl

end

end PolynomialDifferential

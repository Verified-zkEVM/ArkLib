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
specialization uses Hasse derivatives and is valid over every commutative semiring.

The definitions and laws are ported from `ArkLib/Data/Polynomial/Differential/Basic.lean` at
ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.
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

@[simp]
theorem differentialSpecializationHom_apply [CommSemiring F]
    (Q : DifferentialPolynomial F d) (P : F[X]) :
    differentialSpecializationHom P Q = differentialSpecialization Q P :=
  rfl

@[simp]
theorem differentialSpecialization_C [CommSemiring F] (a : F) (P : F[X]) :
    differentialSpecialization (d := d) (MvPolynomial.C a) P = Polynomial.C a := by
  simp [differentialSpecialization, differentialSpecializationHom]

@[simp]
theorem differentialSpecialization_x [CommSemiring F] (P : F[X]) :
    differentialSpecialization (d := d) (MvPolynomial.X none) P = Polynomial.X := by
  simp [differentialSpecialization, differentialSpecializationHom]

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

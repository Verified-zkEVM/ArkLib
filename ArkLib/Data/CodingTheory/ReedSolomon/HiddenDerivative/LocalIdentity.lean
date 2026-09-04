/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Substitution
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.DifferentialEquation
import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift
import Mathlib.Data.ZMod.Basic

/-!
# Actual-polynomial identity for the hidden local substitution

This file connects the formal local variables to the Hasse jets of a genuine univariate
polynomial.  At an agreement `P(alpha) = y`, evaluating the unscaled local error at
`Polynomial.normalizedBackwardTaylorError alpha P d` makes the local substitution recover the
shifted Hasse jet of `P`.  The Hasse--Taylor API proves that this candidate-derived error is
divisible by `X^d` over every commutative ring.

For the normalized substitution, `reducedHiddenTaylorError` canonically divides that error by
`X^d`; no witness is left implicit.  The resulting theorem is the actual-polynomial bridge needed
before local coefficient constraints can imply multiplicity.

## References

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Equations (13)--(16).
-/

noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Polynomial

variable {R : Type*} [CommRing R]
variable {d : ℕ}

/-- Evaluate local variables at the displacement `X`, a chosen hidden error, and the moving Hasse
jets of an actual polynomial. -/
def localPolynomialEvaluation (center : R) (P error : R[X]) :
    LocalPolynomial R d →ₐ[R] R[X] :=
  MvPolynomial.aeval fun v : LocalVariable d ↦ match v with
    | none => Polynomial.X
    | some none => error
    | some (some j) => Polynomial.taylor center (Polynomial.hasseDeriv (j.val + 1) P)

@[simp]
theorem localPolynomialEvaluation_T (center : R) (P error : R[X]) :
    localPolynomialEvaluation (d := d) center P error (MvPolynomial.X (localT d)) =
      Polynomial.X := by
  simp [localPolynomialEvaluation, localT]

@[simp]
theorem localPolynomialEvaluation_E (center : R) (P error : R[X]) :
    localPolynomialEvaluation (d := d) center P error (MvPolynomial.X (localE d)) = error := by
  simp [localPolynomialEvaluation, localE, localAux]

@[simp]
theorem localPolynomialEvaluation_Y (center : R) (P error : R[X]) (j : Fin d) :
    localPolynomialEvaluation center P error (MvPolynomial.X (localY j)) =
      Polynomial.taylor center (Polynomial.hasseDeriv (j.val + 1) P) := by
  simp [localPolynomialEvaluation, localY]

/-- Substitute the shifted independent variable and moving Hasse jets into a differential
polynomial.  This name is intentionally distinct from the root solver's unshifted
`differentialSpecialization`. -/
def shiftedJetSubstitution (center : R) (P : R[X]) :
    DifferentialPolynomial R d →ₐ[R] R[X] :=
  MvPolynomial.aeval fun v : JetVariable d ↦ match v with
    | none => Polynomial.C center + Polynomial.X
    | some j => Polynomial.taylor center (Polynomial.hasseDeriv j.val P)

@[simp]
theorem shiftedJetSubstitution_X (center : R) (P : R[X]) :
    shiftedJetSubstitution (d := d) center P (MvPolynomial.X none) =
      Polynomial.C center + Polynomial.X := by
  simp [shiftedJetSubstitution]

@[simp]
theorem shiftedJetSubstitution_Y_zero (center : R) (P : R[X]) :
    shiftedJetSubstitution (d := d) center P (MvPolynomial.X (some 0)) =
      Polynomial.taylor center P := by
  simp [shiftedJetSubstitution]

@[simp]
theorem shiftedJetSubstitution_Y_succ (center : R) (P : R[X]) (j : Fin d) :
    shiftedJetSubstitution center P (MvPolynomial.X (some j.succ)) =
      Polynomial.taylor center (Polynomial.hasseDeriv (j.val + 1) P) := by
  simp [shiftedJetSubstitution]

/-- The local shifted-jet semantics is affine Taylor translation after the root solver's canonical
differential specialization. This is the adapter between the local-contact and root-count lanes. -/
theorem taylorAlgHom_comp_differentialSpecializationHom (center : R) (P : R[X]) :
    (Polynomial.taylorAlgHom center).comp (differentialSpecializationHom (d := d) P) =
      shiftedJetSubstitution (d := d) center P := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp [differentialSpecializationHom, shiftedJetSubstitution]
    ring
  · simp [differentialSpecializationHom, shiftedJetSubstitution]

/-- Polynomial-level form of the canonical-specialization adapter. -/
theorem taylor_differentialSpecialization (Q : DifferentialPolynomial R d)
    (center : R) (P : R[X]) :
    Polynomial.taylor center (differentialSpecialization Q P) =
      shiftedJetSubstitution center P Q := by
  rw [← differentialSpecializationHom_apply]
  change (Polynomial.taylorAlgHom center)
    (differentialSpecializationHom (d := d) P Q) = shiftedJetSubstitution center P Q
  exact DFunLike.congr_fun (taylorAlgHom_comp_differentialSpecializationHom center P) Q

/-- Under actual moving jets, the formal local correction becomes the Hasse--Taylor correction
sum from the reusable polynomial API. -/
theorem localPolynomialEvaluation_localCorrection (center : R) (P error : R[X]) :
    localPolynomialEvaluation center P error (localCorrection d) =
      Polynomial.movingHasseSum center P d := by
  rw [localCorrection, map_sum, Polynomial.movingHasseSum]
  let term : ℕ → R[X] := fun j ↦
    Polynomial.C ((-1 : R) ^ j) *
      (Polynomial.X ^ (j + 1) *
        Polynomial.taylor center (Polynomial.hasseDeriv (j + 1) P))
  change (∑ j : Fin d,
    localPolynomialEvaluation center P error
      (MvPolynomial.C ((-1 : R) ^ j.val) *
        MvPolynomial.X (localT d) ^ (j.val + 1) * MvPolynomial.X (localY j))) =
      ∑ j ∈ Finset.range d, term j
  rw [← Fin.sum_univ_eq_sum_range (f := term) (n := d)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul, map_pow, algHom_C,
    localPolynomialEvaluation_T, localPolynomialEvaluation_Y]
  dsimp [term]
  rw [← map_pow]
  ring

/-- A reconstruction identity is exactly the generator-level condition needed for unscaled local
substitution to recover the shifted jet. -/
theorem localPolynomialEvaluation_comp_unscaled_of_reconstruction
    (center received : R) (P error : R[X])
    (hreconstruction :
      Polynomial.taylor center P = Polynomial.C received +
        Polynomial.movingHasseSum center P d + Polynomial.X * error) :
    (localPolynomialEvaluation center P error).comp
        (unscaledLocalSubstitution d center received) =
      shiftedJetSubstitution center P := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [AlgHom.coe_comp, Function.comp_apply, unscaledLocalSubstitution_Y_zero,
        map_add, map_mul, algHom_C, localPolynomialEvaluation_localCorrection,
        localPolynomialEvaluation_T, localPolynomialEvaluation_E,
        shiftedJetSubstitution_Y_zero]
      exact hreconstruction.symm
    · simp

/-- At an agreement point, evaluating the unscaled substitution at the candidate-derived hidden
error recovers the actual shifted jet. -/
theorem localPolynomialEvaluation_comp_unscaled_backwardError
    (center received : R) (P : R[X]) (hP : P.eval center = received) :
    (localPolynomialEvaluation center P
        (Polynomial.normalizedBackwardTaylorError center P d)).comp
        (unscaledLocalSubstitution d center received) =
      shiftedJetSubstitution center P := by
  apply localPolynomialEvaluation_comp_unscaled_of_reconstruction
  exact Polynomial.backwardTaylorReconstruction_of_eval_eq d hP

/-- Polynomial-level form of the unscaled actual-polynomial identity. -/
theorem localPolynomialEvaluation_unscaled_backwardError
    (Q : DifferentialPolynomial R d) (center received : R) (P : R[X])
    (hP : P.eval center = received) :
    localPolynomialEvaluation center P
        (Polynomial.normalizedBackwardTaylorError center P d)
        (unscaledLocalSubstitution d center received Q) =
      shiftedJetSubstitution center P Q :=
  DFunLike.congr_fun
    (localPolynomialEvaluation_comp_unscaled_backwardError center received P hP) Q

/-- The candidate-derived hidden error is divisible by `X^d`; this is characteristic-safe. -/
theorem X_pow_dvd_hiddenTaylorError (center : R) (P : R[X]) :
    Polynomial.X ^ d ∣ Polynomial.normalizedBackwardTaylorError center P d :=
  Polynomial.X_pow_dvd_normalizedBackwardTaylorError center P d

/-- Canonical quotient of the hidden Taylor error after removing its guaranteed `X^d` factor. -/
def reducedHiddenTaylorError (center : R) (P : R[X]) (d : ℕ) : R[X] :=
  Polynomial.normalizedBackwardTaylorError center P d /ₘ (Polynomial.X ^ d)

/-- Multiplying the canonical reduced error by `X^d` recovers the hidden Taylor error. -/
theorem X_pow_mul_reducedHiddenTaylorError (center : R) (P : R[X]) (d : ℕ) :
    Polynomial.X ^ d * reducedHiddenTaylorError center P d =
      Polynomial.normalizedBackwardTaylorError center P d := by
  have hmod :
      Polynomial.normalizedBackwardTaylorError center P d %ₘ (Polynomial.X ^ d) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow d)).2
      (Polynomial.X_pow_dvd_normalizedBackwardTaylorError center P d)
  simpa [reducedHiddenTaylorError, hmod] using
    Polynomial.modByMonic_add_div
      (Polynomial.normalizedBackwardTaylorError center P d) (Polynomial.X ^ d)

/-- The normalized error term `X^(d+1) E` evaluates to `X` times the unscaled hidden error. -/
theorem X_pow_succ_mul_reducedHiddenTaylorError (center : R) (P : R[X]) (d : ℕ) :
    Polynomial.X ^ (d + 1) * reducedHiddenTaylorError center P d =
      Polynomial.X * Polynomial.normalizedBackwardTaylorError center P d := by
  calc
    Polynomial.X ^ (d + 1) * reducedHiddenTaylorError center P d =
        Polynomial.X *
          (Polynomial.X ^ d * reducedHiddenTaylorError center P d) := by
      rw [pow_succ]
      ring
    _ = _ := by rw [X_pow_mul_reducedHiddenTaylorError]

/-- A normalized reconstruction identity is the generator-level condition needed for normalized
local substitution to recover the shifted jet. -/
theorem localPolynomialEvaluation_comp_normalized_of_reconstruction
    (center received : R) (P reducedError : R[X])
    (hreconstruction :
      Polynomial.taylor center P = Polynomial.C received +
        Polynomial.movingHasseSum center P d + Polynomial.X ^ (d + 1) * reducedError) :
    (localPolynomialEvaluation center P reducedError).comp
        (normalizedLocalSubstitution d center received) =
      shiftedJetSubstitution center P := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp only [AlgHom.coe_comp, Function.comp_apply, normalizedLocalSubstitution_Y_zero,
        map_add, map_mul, map_pow, algHom_C,
        localPolynomialEvaluation_localCorrection, localPolynomialEvaluation_T,
        localPolynomialEvaluation_E, shiftedJetSubstitution_Y_zero]
      exact hreconstruction.symm
    · simp

/-- At an agreement point, evaluating the normalized substitution at the canonical reduced error
recovers the actual shifted jet. -/
theorem localPolynomialEvaluation_comp_normalized_reducedError
    (center received : R) (P : R[X]) (hP : P.eval center = received) :
    (localPolynomialEvaluation center P (reducedHiddenTaylorError center P d)).comp
        (normalizedLocalSubstitution d center received) =
      shiftedJetSubstitution center P := by
  apply localPolynomialEvaluation_comp_normalized_of_reconstruction
  rw [X_pow_succ_mul_reducedHiddenTaylorError]
  exact Polynomial.backwardTaylorReconstruction_of_eval_eq d hP

/-- Polynomial-level form of the normalized actual-polynomial identity. -/
theorem localPolynomialEvaluation_normalized_reducedError
    (Q : DifferentialPolynomial R d) (center received : R) (P : R[X])
    (hP : P.eval center = received) :
    localPolynomialEvaluation center P (reducedHiddenTaylorError center P d)
        (normalizedLocalSubstitution d center received Q) =
      shiftedJetSubstitution center P Q :=
  DFunLike.congr_fun
    (localPolynomialEvaluation_comp_normalized_reducedError center received P hP) Q

/-! ### Small-order canaries -/

/-- In characteristic two the Hasse identity remains valid: no factorial denominator or
characteristic lower bound is present in the local bridge. -/
theorem characteristic_two_local_identity_canary
    (Q : DifferentialPolynomial (ZMod 2) 2) (P : (ZMod 2)[X])
    (hP : P.eval 1 = 0) :
    localPolynomialEvaluation 1 P
        (Polynomial.normalizedBackwardTaylorError 1 P 2)
        (unscaledLocalSubstitution 2 1 0 Q) =
      shiftedJetSubstitution 1 P Q :=
  localPolynomialEvaluation_unscaled_backwardError Q 1 0 P hP

end ReedSolomon.HiddenDerivative

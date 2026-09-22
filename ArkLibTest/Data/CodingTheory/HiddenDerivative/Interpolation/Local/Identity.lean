/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Identity

/-!
# Local backward-error identity acceptance tests

* The agreement hypothesis `P(center) = received` is necessary: if the unscaled identity holds
  for some error, then evaluating the reconstruction at `X = 0` gives `P(center) = received`. In
  particular for `P = 1` and `received = 0` no error works.
* For `P = X²` and `d = 1` the backward Taylor error at `a` is `-X`, obtained from the uniqueness
  statement `localPolynomialEvaluation_comp_unscaled_eq_iff_error_eq`.
* The source-shaped statement: the local evaluation of the unscaled substitution of `Q` is the
  Taylor translate of `Q(X, P, D¹P, ...)`.
* The source's `X_pow_dvd_hiddenTaylorError`, derived from the reduced error.
* The algebra-valued criterion at `d = 0`, with `ℤ`-coefficients evaluated in `ℚ`.
-/

open MvPolynomial PolynomialDifferential ReedSolomon.HiddenDerivative

namespace LocalIdentityTest

/-- The unscaled identity forces `P(center) = received`. -/
theorem identity_forces_agreement {d : ℕ} (center received : ℚ) (P error : Polynomial ℚ)
    (h : (localPolynomialEvaluation center P error).comp
        (unscaledLocalSubstitution d center received) = shiftedJetSubstitution center P) :
    P.eval center = received := by
  have h0 := congrArg (Polynomial.eval 0)
    ((localPolynomialEvaluation_comp_unscaled_eq_iff center received P error).mp h)
  simpa [Polynomial.taylor_eval, Polynomial.movingHasseSum, Polynomial.eval_finsetSum] using h0

/-- For `P = 1` and `received = 0` no error satisfies the unscaled identity. -/
example (d : ℕ) (center : ℚ) (error : Polynomial ℚ) :
    (localPolynomialEvaluation center 1 error).comp (unscaledLocalSubstitution d center 0) ≠
      shiftedJetSubstitution center 1 := fun h => by
  simpa using identity_forces_agreement center 0 1 error h

/-- For `P = X²` and `d = 1` the backward Taylor error at `a` is `-X`: indeed
`(a + X)² = a² + X · 2(a + X) + X · (-X)`. -/
example (a : ℚ) :
    Polynomial.normalizedBackwardTaylorError a (Polynomial.X ^ 2) 1 = -Polynomial.X := by
  have hP : (Polynomial.X ^ 2 : Polynomial ℚ).eval a = a ^ 2 := by simp
  refine ((localPolynomialEvaluation_comp_unscaled_eq_iff_error_eq (d := 1) a (a ^ 2) _ _
    hP).mp ?_).symm
  rw [localPolynomialEvaluation_comp_unscaled_eq_iff, Polynomial.movingHasseSum_one,
    Polynomial.derivative_X_pow]
  simp only [Polynomial.taylor_pow, Polynomial.taylor_mul, Polynomial.taylor_X,
    Polynomial.taylor_C, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Polynomial.C_pow]
  simp only [Polynomial.C_ofNat]
  ring

/-- Source shape: the local evaluation of the unscaled substitution of `Q` is the Taylor
translate of the differential specialization of `Q` at `P`. -/
example {d : ℕ} (Q : DifferentialPolynomial ℚ d) (center : ℚ) (P : Polynomial ℚ) :
    localPolynomialEvaluation center P (Polynomial.normalizedBackwardTaylorError center P d)
        (unscaledLocalSubstitution d center (P.eval center) Q) =
      Polynomial.taylor center (differentialSpecialization Q P) := by
  rw [taylor_differentialSpecialization,
    localPolynomialEvaluation_unscaled_backwardError Q center _ P rfl]

/-- Source shape of `X_pow_dvd_hiddenTaylorError`, over `ℤ`. -/
example (d : ℕ) (center : ℤ) (P : Polynomial ℤ) :
    Polynomial.X ^ d ∣ Polynomial.normalizedBackwardTaylorError center P d :=
  ⟨_, (X_pow_mul_reducedHiddenTaylorError center P d).symm⟩

/-- The algebra-valued criterion at `d = 0`, with `ℤ` coefficients and values in `ℚ`: the
evaluation `T ↦ t, E ↦ e` after the unscaled substitution at `(2, 3)` is the evaluation
`X ↦ 2 + t, Y₀ ↦ 3 + t e`. -/
example (t e : ℚ) :
    (aeval (fun v : LocalVariable 0 => Option.elim v t fun _ => e)).comp
        (unscaledLocalSubstitution 0 (2 : ℤ) 3) =
      aeval (fun v : JetVariable 0 => Option.elim v (2 + t) fun _ => 3 + t * e) := by
  rw [aeval_comp_unscaledLocalSubstitution_eq_aeval_iff]
  refine ⟨by simp [localT], ?_, fun j => j.elim0⟩
  simp [localT, localE, localAux, localCorrection]

end LocalIdentityTest

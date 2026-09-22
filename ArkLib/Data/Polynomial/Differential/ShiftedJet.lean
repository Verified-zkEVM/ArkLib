/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.Basic
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Shifted-jet substitution

For a center `a` and a polynomial `P`, the shifted-jet substitution sends a differential
polynomial `Q(X, Y₀, ..., Y_d)` to

```text
Q(a + X, P(a + X), (D¹P)(a + X), ..., (DᵈP)(a + X)),
```

where `Dʲ` is the `j`-th Hasse derivative. It describes `Q(X, P, D¹P, ...)` in the displacement
coordinate `X - a`: by `taylor_differentialSpecialization` it is the Taylor translate of the
differential specialization of `Q` at `P`. Every statement holds over a commutative semiring.

## Main statements

* `shiftedJetSubstitution`: the substitution, with its generator images.
* `taylorAlgHom_comp_differentialSpecializationHom`: Taylor translation after differential
  specialization is the shifted-jet substitution.
* `taylor_differentialSpecialization`: the same identity applied to one polynomial.
* `coeff_zero_shiftedJetSubstitution`: the constant coefficient is the jet evaluation at the
  center.

## References

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/Identity.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `shiftedJetSubstitution`,
`shiftedJetSubstitution_X`, `shiftedJetSubstitution_Y_zero`, `shiftedJetSubstitution_Y_succ`,
`taylorAlgHom_comp_differentialSpecializationHom`, and `taylor_differentialSpecialization`. The
source stated them over a commutative ring in the namespace `ReedSolomon.HiddenDerivative`; they
mention no Reed–Solomon object, so they are stated here over a commutative semiring, next to the
differential specialization they translate. Nothing is deferred.

`coeff_zero_shiftedJetSubstitution` generalizes the source's
`eval_zero_shiftedJetSubstitution_separant` in
`.../HiddenDerivative/RootFinding/Regular/Lifting.lean` from the separant over a field to any
differential polynomial over a commutative semiring.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-- The shifted-jet substitution at center `a`: `X ↦ a + X` and `Y_j ↦ (DʲP)(a + X)`, where
`Dʲ` is the `j`-th Hasse derivative. -/
def shiftedJetSubstitution (center : R) (P : R[X]) :
    DifferentialPolynomial R d →ₐ[R] R[X] :=
  MvPolynomial.aeval fun v : JetVariable d ↦ match v with
    | none => C center + X
    | some j => taylor center (hasseDeriv j.val P)

@[simp]
theorem shiftedJetSubstitution_X (center : R) (P : R[X]) :
    shiftedJetSubstitution (d := d) center P (MvPolynomial.X none) = C center + X := by
  simp [shiftedJetSubstitution]

@[simp]
theorem shiftedJetSubstitution_Y (center : R) (P : R[X]) (j : Fin (d + 1)) :
    shiftedJetSubstitution center P (MvPolynomial.X (some j)) =
      taylor center (hasseDeriv j.val P) := by
  simp [shiftedJetSubstitution]

/-- `Y₀` is sent to the translate `P(a + X)`. -/
theorem shiftedJetSubstitution_Y_zero (center : R) (P : R[X]) :
    shiftedJetSubstitution (d := d) center P (MvPolynomial.X (some 0)) = taylor center P := by
  simp

/-- `Y_(j+1)` is sent to the translate of the `(j+1)`-th Hasse derivative. -/
theorem shiftedJetSubstitution_Y_succ (center : R) (P : R[X]) (j : Fin d) :
    shiftedJetSubstitution center P (MvPolynomial.X (some j.succ)) =
      taylor center (hasseDeriv (j.val + 1) P) := by
  simp

/-- Taylor translation by `a` after differential specialization at `P` is the shifted-jet
substitution at `a`. On `X` this is `taylor a X = X + C a`; on `Y_j` it is the definition. -/
theorem taylorAlgHom_comp_differentialSpecializationHom (center : R) (P : R[X]) :
    (taylorAlgHom center).comp (differentialSpecializationHom (d := d) P) =
      shiftedJetSubstitution center P := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with _ | j
  · simp [differentialSpecializationHom, add_comm]
  · simp [differentialSpecializationHom]

/-- The shifted-jet substitution of `Q` is the Taylor translate of `Q(X, P, D¹P, ..., DᵈP)`. -/
theorem taylor_differentialSpecialization (Q : DifferentialPolynomial R d) (center : R)
    (P : R[X]) :
    taylor center (differentialSpecialization Q P) = shiftedJetSubstitution center P Q := by
  rw [← taylorAlgHom_comp_differentialSpecializationHom, AlgHom.comp_apply,
    differentialSpecializationHom_apply]
  rfl

/-- The constant coefficient of the shifted-jet substitution is `Q` evaluated at the center and
the Hasse jet of `P` there. -/
theorem coeff_zero_shiftedJetSubstitution (Q : DifferentialPolynomial R d) (center : R)
    (P : R[X]) :
    (shiftedJetSubstitution center P Q).coeff 0 =
      jetEvaluation Q center (polynomialJet center P) := by
  rw [← taylor_differentialSpecialization, taylor_coeff_zero, eval_differentialSpecialization]

end

end PolynomialDifferential

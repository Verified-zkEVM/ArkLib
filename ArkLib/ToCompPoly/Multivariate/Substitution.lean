/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import CompPoly.Multivariate.Operations
/-!
# Semantic correctness of computable multivariate substitution

CompPoly provides the executable `CMvPolynomial.bind₁`. This file proves that converting its
result agrees with `MvPolynomial.aeval`, so symbolic chart constructors may remain computable
while reusing the existing semantic Taylor theorems.
-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Computable substitution agrees with semantic multivariate evaluation. -/
theorem fromCMvPolynomial_bind₁ {n m : ℕ} (f : Fin n → CMvPolynomial m R)
    (p : CMvPolynomial n R) :
    fromCMvPolynomial (bind₁ f p) =
      MvPolynomial.aeval (fun i => fromCMvPolynomial (f i)) (fromCMvPolynomial p) := by
  rw [bind₁_eq_aeval]
  change fromCMvPolynomial (CMvPolynomial.eval₂ (algebraMap R _) f p) = _
  rw [CPoly.eval₂_equiv]
  change CPoly.polyRingEquiv
      (MvPolynomial.aeval f (fromCMvPolynomial p)) = _
  have hmap := MvPolynomial.map_aeval f CPoly.polyRingEquiv.toRingHom
    (fromCMvPolynomial p)
  have hcoeff : CPoly.polyRingEquiv.toRingHom.comp
      (algebraMap R (CMvPolynomial m R)) =
      algebraMap R (MvPolynomial (Fin m) R) := by
    apply RingHom.ext
    intro coefficient
    exact CPoly.CMvPolynomial.fromCMvPolynomial_C coefficient
  rw [hcoeff] at hmap
  exact hmap

end CPoly.CMvPolynomial

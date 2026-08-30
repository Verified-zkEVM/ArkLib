/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Multivariate.Operations

/-!
  # Evaluation of computable multivariate polynomials, bundled and over `Finset`s

  Additions to `CompPoly.Multivariate.CMvPolynomialEvalLemmas`, not yet upstreamed to CompPoly.

  CompPoly records that `CMvPolynomial.eval vals` respects each ring operation separately
  (`eval_zero`, `eval_one`, `eval_add`, `eval_mul`, `eval_C`, …), which is what `simp`/`grind`
  need to normalize a *fixed* expression. Two things are missing for reasoning about a **family**
  of polynomials: the value of a bare variable, and commutation with `Finset.sum` / `Finset.prod`.

  Both follow at once from bundling: `CMvPolynomial.eval vals` is `eval₂Hom (RingHom.id R) vals`,
  so `map_sum` and `map_prod` apply verbatim. `evalHom` records that bundling; the two `Finset`
  lemmas are its immediate corollaries, stated in unbundled form so that call sites can rewrite
  without unfolding.

  These are the lemmas the Hachi sumcheck summands need
  (`Commitments/Functional/Hachi/ZeroCheck/Constraints.lean`): its constraint polynomials are
  built as a sum over the Boolean cube of a coefficient times a product of linear factors, so
  every evaluation argument crosses both a `Finset.sum` and a `Finset.prod`.
-/

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R] (vals : Fin n → R)

/-- Evaluation at a fixed point, bundled as a ring homomorphism — the identity-coefficient case
of `eval₂Hom`. This is what gives evaluation the `map_*` API of a `RingHom`. -/
def evalHom : CMvPolynomial n R →+* R := eval₂Hom (RingHom.id R) vals

@[simp]
theorem evalHom_apply (p : CMvPolynomial n R) : evalHom vals p = p.eval vals := rfl

/-- Evaluating a bare variable returns the corresponding coordinate. -/
@[simp]
theorem eval_X (i : Fin n) : (X (R := R) i).eval vals = vals i := by
  rw [eval_equiv, fromCMvPolynomial_X, MvPolynomial.eval_X]

/-- Evaluation commutes with a finite sum of polynomials. -/
theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial n R) :
    (∑ i ∈ s, f i).eval vals = ∑ i ∈ s, (f i).eval vals :=
  map_sum (evalHom vals) f s

/-- Evaluation commutes with a finite product of polynomials. -/
theorem eval_prod {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial n R) :
    (∏ i ∈ s, f i).eval vals = ∏ i ∈ s, (f i).eval vals :=
  map_prod (evalHom vals) f s

/-! ## Transporting a whole polynomial

The lemmas above are enough for statements about *values*. A statement about *degrees* is not
determined by values (two distinct polynomials agree everywhere over a finite field), so it has to
cross the representation boundary at the level of the polynomial itself, through
`fromCMvPolynomial`. That map is the forward direction of `polyRingEquiv`, hence a ring
homomorphism, so it too commutes with `Finset.sum` and `Finset.prod`. -/

/-- `fromCMvPolynomial` commutes with a finite sum. -/
theorem fromCMvPolynomial_sum {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial n R) :
    fromCMvPolynomial (∑ i ∈ s, f i) = ∑ i ∈ s, fromCMvPolynomial (f i) :=
  map_sum (polyRingEquiv (n := n) (R := R)) f s

/-- `fromCMvPolynomial` commutes with a finite product. -/
theorem fromCMvPolynomial_prod {ι : Type*} (s : Finset ι) (f : ι → CMvPolynomial n R) :
    fromCMvPolynomial (∏ i ∈ s, f i) = ∏ i ∈ s, fromCMvPolynomial (f i) :=
  map_prod (polyRingEquiv (n := n) (R := R)) f s

/-- `fromCMvPolynomial` commutes with addition, in `HAdd` notation. CompPoly's own `CPoly.map_add`
is stated at `Add.add`, which `rw` will not match against a `+` written by the elaborator. -/
theorem fromCMvPolynomial_add' (p q : CMvPolynomial n R) :
    fromCMvPolynomial (p + q) = fromCMvPolynomial p + fromCMvPolynomial q :=
  _root_.map_add (polyRingEquiv (n := n) (R := R)) p q

/-- `fromCMvPolynomial` commutes with multiplication, in `HMul` notation. -/
theorem fromCMvPolynomial_mul' (p q : CMvPolynomial n R) :
    fromCMvPolynomial (p * q) = fromCMvPolynomial p * fromCMvPolynomial q :=
  _root_.map_mul (polyRingEquiv (n := n) (R := R)) p q

/-- `fromCMvPolynomial` sends `1` to `1`. -/
theorem fromCMvPolynomial_one' :
    fromCMvPolynomial (1 : CMvPolynomial n R) = 1 :=
  _root_.map_one (polyRingEquiv (n := n) (R := R))

end CPoly.CMvPolynomial

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type*} [CommRing R] [BEq R] [LawfulBEq R]

/-- `fromCMvPolynomial` commutes with subtraction, in `HSub` notation. -/
theorem fromCMvPolynomial_sub' (p q : CMvPolynomial n R) :
    fromCMvPolynomial (p - q) = fromCMvPolynomial p - fromCMvPolynomial q :=
  _root_.map_sub (polyRingEquiv (n := n) (R := R)) p q

end CPoly.CMvPolynomial

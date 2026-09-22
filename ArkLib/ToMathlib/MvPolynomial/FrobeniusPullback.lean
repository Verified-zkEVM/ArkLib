/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Inverse Frobenius coefficient twist and variable power substitution

Let `R` be a perfect ring of exponential characteristic `p`, and let `s = p ^ e`. For a
multivariate polynomial `G` over `R`, the inverse Frobenius coefficient twist
`inverseFrobeniusTwist p e G` applies the inverse of `x ↦ x ^ s` to every coefficient of `G`.
Raising it to the power `s` gives `G.expand s`, the substitution of `X i ^ s` for every
variable. Consequently a point `v` with `G (v ^ s) = 0` is a root of the twist.

The substitution of `X i ^ q i` for each variable `X i`, with variable-dependent exponents `q`, is
`variablePowerSubstitution q`. Exponent functions compose by pointwise multiplication. If
`F = variablePowerSubstitution r G` substitutes powers into some variables of `G`, and `q` supplies
the complementary exponents with `q i * r i = s` for every `i`, then the `s`-th power of the twist
of `G` is `variablePowerSubstitution q F`. With three variables and `r` the exponent `s` on the
last variable only, this is the identity `G̃(T, W, U) ^ s = F(T ^ s, W ^ s, U)` for
`F(X, Z, Y) = G(X, Z, Y ^ s)`.

The twist is `MvPolynomial.map` along a ring automorphism, so it preserves irreducibility, every
individual degree, and commutes with partial derivatives.

## Main statements

* `MvPolynomial.inverseFrobeniusTwist_pow`:
  `inverseFrobeniusTwist p e G ^ p ^ e = G.expand (p ^ e)`.
* `MvPolynomial.eval_inverseFrobeniusTwist_eq_zero`: root transport along the twist.
* `MvPolynomial.variablePowerSubstitution_comp` and `MvPolynomial.eval_variablePowerSubstitution`.
* `MvPolynomial.inverseFrobeniusTwist_pow_eq_variablePowerSubstitution` and
  `MvPolynomial.eval_inverseFrobeniusTwist_eq_zero_of_variablePowerSubstitution`: the identity
  and root transport for a split between complementary exponents.
* `MvPolynomial.irreducible_inverseFrobeniusTwist_iff`,
  `MvPolynomial.degreeOf_inverseFrobeniusTwist` and `MvPolynomial.pderiv_inverseFrobeniusTwist`.
* `MvPolynomial.degreeOf_map_of_injective`: an injective coefficient map preserves every
  individual degree.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

section MapDegree

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

/-- An injective coefficient map preserves the degree in every variable. -/
theorem degreeOf_map_of_injective {f : R →+* S} (hf : Function.Injective f)
    (G : MvPolynomial σ R) (i : σ) : degreeOf i (map f G) = degreeOf i G := by
  classical
  simp only [degreeOf_def, degrees_map_of_injective G hf]

end MapDegree

section VariablePowerSubstitution

variable {R τ : Type*} [CommSemiring R]

/-- Substitute `X i ^ q i` for each variable `X i`. -/
def variablePowerSubstitution (q : τ → ℕ) : MvPolynomial τ R →ₐ[R] MvPolynomial τ R :=
  bind₁ fun i ↦ X i ^ q i

/-- `variablePowerSubstitution q` sends `X i` to `X i ^ q i`. -/
@[simp]
theorem variablePowerSubstitution_X (q : τ → ℕ) (i : τ) :
    variablePowerSubstitution q (X i : MvPolynomial τ R) = X i ^ q i :=
  bind₁_X_right _ i

/-- Variable power substitutions compose by multiplying their exponents pointwise. -/
theorem variablePowerSubstitution_comp (q r : τ → ℕ) (G : MvPolynomial τ R) :
    variablePowerSubstitution q (variablePowerSubstitution r G) =
      variablePowerSubstitution (fun i ↦ q i * r i) G := by
  simp only [variablePowerSubstitution, bind₁_bind₁, map_pow, bind₁_X_right, pow_mul]

/-- Substituting the same power `X i ^ s` into every variable is `MvPolynomial.expand s`. -/
theorem variablePowerSubstitution_const (s : ℕ) (G : MvPolynomial τ R) :
    variablePowerSubstitution (fun _ ↦ s) G = G.expand s := by
  apply DFunLike.congr_fun (algHom_ext fun i ↦ ?_) G
  simp

/-- Evaluating `variablePowerSubstitution q G` at `v` evaluates `G` at `i ↦ v i ^ q i`. -/
theorem eval_variablePowerSubstitution (q : τ → ℕ) (G : MvPolynomial τ R) (v : τ → R) :
    eval v (variablePowerSubstitution q G) = eval (fun i ↦ v i ^ q i) G := by
  rw [variablePowerSubstitution]
  change eval v (eval₂ C (fun i ↦ X i ^ q i) G) = _
  rw [← eval_assoc]
  simp [Function.comp_def]

end VariablePowerSubstitution

section InverseFrobeniusTwist

variable {R σ : Type*} [CommSemiring R] (p e : ℕ) [ExpChar R p] [PerfectRing R p]

/-- Apply the inverse of the `e`-fold Frobenius `x ↦ x ^ p ^ e` to every coefficient. -/
def inverseFrobeniusTwist (G : MvPolynomial σ R) : MvPolynomial σ R :=
  G.map (iterateFrobeniusEquiv R p e).symm

/-- The `p ^ e`-th power of the inverse Frobenius coefficient twist is the substitution of
`X i ^ p ^ e` for every variable. -/
theorem inverseFrobeniusTwist_pow (G : MvPolynomial σ R) :
    inverseFrobeniusTwist p e G ^ p ^ e = G.expand (p ^ e) := by
  have hcomp : (iterateFrobenius R p e).comp (iterateFrobeniusEquiv R p e).symm =
      RingHom.id R := by
    ext x
    exact (iterateFrobeniusEquiv R p e).apply_symm_apply x
  simpa only [inverseFrobeniusTwist, map_expand, map_map, hcomp, map_id] using
    (map_iterateFrobenius_expand p (inverseFrobeniusTwist p e G) e).symm

/-- The inverse Frobenius coefficient twist vanishes only at zero. -/
theorem inverseFrobeniusTwist_eq_zero_iff {G : MvPolynomial σ R} :
    inverseFrobeniusTwist p e G = 0 ↔ G = 0 :=
  map_eq_zero_iff _ (map_injective _ (iterateFrobeniusEquiv R p e).symm.injective)

/-- The inverse Frobenius coefficient twist is irreducible exactly when the polynomial is. -/
theorem irreducible_inverseFrobeniusTwist_iff {G : MvPolynomial σ R} :
    Irreducible (inverseFrobeniusTwist p e G) ↔ Irreducible G :=
  MulEquiv.irreducible_iff (mapEquiv σ (iterateFrobeniusEquiv R p e).symm)

/-- Evaluating the twist at `v` and raising to the power `p ^ e` evaluates `G` at `v ^ p ^ e`. -/
theorem eval_inverseFrobeniusTwist_pow (G : MvPolynomial σ R) (v : σ → R) :
    eval v (inverseFrobeniusTwist p e G) ^ p ^ e = eval (v ^ p ^ e) G := by
  rw [← eval_pow, inverseFrobeniusTwist_pow, eval_expand]

/-- If `G` vanishes at `v ^ p ^ e`, then the twist of `G` vanishes at `v`. -/
theorem eval_inverseFrobeniusTwist_eq_zero (G : MvPolynomial σ R) (v : σ → R)
    (hG : eval (v ^ p ^ e) G = 0) : eval v (inverseFrobeniusTwist p e G) = 0 := by
  apply (map_eq_zero_iff (iterateFrobeniusEquiv R p e)
    (iterateFrobeniusEquiv R p e).injective).mp
  rw [iterateFrobeniusEquiv_def, eval_inverseFrobeniusTwist_pow, hG]

/-- Let `F = variablePowerSubstitution r G`, and let `q` be complementary exponents with
`q i * r i = p ^ e` for every variable. Then the `p ^ e`-th power of the twist of `G` is
`variablePowerSubstitution q F`. -/
theorem inverseFrobeniusTwist_pow_eq_variablePowerSubstitution {q r : σ → ℕ}
    (hqr : ∀ i, q i * r i = p ^ e) {F G : MvPolynomial σ R}
    (hF : F = variablePowerSubstitution r G) :
    inverseFrobeniusTwist p e G ^ p ^ e = variablePowerSubstitution q F := by
  rw [hF, variablePowerSubstitution_comp, inverseFrobeniusTwist_pow,
    ← variablePowerSubstitution_const]
  congr
  funext i
  exact (hqr i).symm

/-- Root transport for complementary exponents: if `F = variablePowerSubstitution r G`,
`q i * r i = p ^ e` for every `i`, and `F` vanishes at `i ↦ v i ^ q i`, then the twist of `G`
vanishes at `v`. -/
theorem eval_inverseFrobeniusTwist_eq_zero_of_variablePowerSubstitution {q r : σ → ℕ}
    (hqr : ∀ i, q i * r i = p ^ e) {F G : MvPolynomial σ R}
    (hF : F = variablePowerSubstitution r G) (v : σ → R)
    (hroot : eval (fun i ↦ v i ^ q i) F = 0) :
    eval v (inverseFrobeniusTwist p e G) = 0 := by
  apply (map_eq_zero_iff (iterateFrobeniusEquiv R p e)
    (iterateFrobeniusEquiv R p e).injective).mp
  rw [iterateFrobeniusEquiv_def, ← eval_pow,
    inverseFrobeniusTwist_pow_eq_variablePowerSubstitution p e hqr hF,
    eval_variablePowerSubstitution, hroot]

/-- The inverse Frobenius coefficient twist preserves the degree in every variable. -/
theorem degreeOf_inverseFrobeniusTwist (G : MvPolynomial σ R) (i : σ) :
    degreeOf i (inverseFrobeniusTwist p e G) = degreeOf i G :=
  degreeOf_map_of_injective (iterateFrobeniusEquiv R p e).symm.injective G i

/-- The inverse Frobenius coefficient twist commutes with every partial derivative. -/
theorem pderiv_inverseFrobeniusTwist (G : MvPolynomial σ R) (i : σ) :
    pderiv i (inverseFrobeniusTwist p e G) = inverseFrobeniusTwist p e (pderiv i G) :=
  pderiv_map

/-- A partial derivative of the twist is nonzero exactly when that partial derivative of the
polynomial is nonzero. -/
theorem pderiv_inverseFrobeniusTwist_ne_zero_iff (G : MvPolynomial σ R) (i : σ) :
    pderiv i (inverseFrobeniusTwist p e G) ≠ 0 ↔ pderiv i G ≠ 0 := by
  rw [pderiv_inverseFrobeniusTwist, ne_eq, inverseFrobeniusTwist_eq_zero_iff]

end InverseFrobeniusTwist

end

end MvPolynomial

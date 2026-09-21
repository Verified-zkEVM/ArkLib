/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight

/-!
# Local variables and weights for hidden-derivative interpolation

After translating a differential polynomial to an agreement point, the hidden-derivative argument
works with polynomials in the following local variables:

* `localT d`, the displacement `T`;
* `localU d = localE d`, one auxiliary slot, called `U` before the hidden-derivative rewrite and
  `E` (the hidden error) afterwards;
* `localY j` for `j : Fin d`, the visible jet `Y_(j+1)`.

Two weights on these variables govern the local constraints. The contact weight gives `T`
weight one, `E` weight `d`, and every visible jet weight zero, so the monomial `T^i E^b Y^c` has
contact order `i + d * b`. The `T`-weight counts only the exponent of `T`.

## References

The definitions are ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/
Variables.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `LocalVariable`,
`LocalPolynomial`, `localT`, `localAux`, `localU`, `localE`, `localY`, `localContactWeight`,
`localContactOrder`, and `localTWeight`, with their evaluation lemmas. The source also defined
higher-jet and derivative-order local weights, the global weight `jetHigherWeight`, and the
substitution caps `localSubstitutionSourceWeight`; the global weight moves to
`ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Index`, and the others are
deferred to the slices that use them.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d : ℕ}

/-- Variables of a local expansion: `none` is `T`, `some none` is the auxiliary slot, and
`some (some j)` is the visible jet `Y_(j+1)`. -/
abbrev LocalVariable (d : ℕ) := Option (Option (Fin d))

/-- Polynomials in `T`, one auxiliary variable, and the visible jets `Y₁, ..., Y_d`. -/
abbrev LocalPolynomial (R : Type*) [CommSemiring R] (d : ℕ) :=
  MvPolynomial (LocalVariable d) R

/-- The local displacement variable `T`. -/
def localT (d : ℕ) : LocalVariable d := none

/-- The shared auxiliary slot. -/
def localAux (d : ℕ) : LocalVariable d := some none

/-- The auxiliary slot before it is rewritten in terms of the hidden error. -/
abbrev localU (d : ℕ) : LocalVariable d := localAux d

/-- The auxiliary slot after the rewrite, where it holds the hidden error. -/
abbrev localE (d : ℕ) : LocalVariable d := localAux d

/-- The local variable for the visible jet `Y_(j+1)`. -/
def localY {d : ℕ} (j : Fin d) : LocalVariable d := some (some j)

/-- Contact weights: `T` has weight one, `E` has weight `d`, and visible jets have weight zero. -/
def localContactWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some none => d
  | some (some _) => 0

@[simp]
theorem localContactWeight_T (d : ℕ) : localContactWeight d (localT d) = 1 := rfl

@[simp]
theorem localContactWeight_E (d : ℕ) : localContactWeight d (localE d) = d := rfl

@[simp]
theorem localContactWeight_Y (j : Fin d) : localContactWeight d (localY j) = 0 := rfl

/-- The contact order of a local monomial: `T^i E^b Y^c` has contact order `i + d * b`. -/
def localContactOrder (d : ℕ) (e : LocalVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (localContactWeight d) e

/-- The weight that counts only the exponent of `T`. -/
def localTWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some _ => 0

@[simp]
theorem localTWeight_T (d : ℕ) : localTWeight d (localT d) = 1 := rfl

@[simp]
theorem localTWeight_E (d : ℕ) : localTWeight d (localE d) = 0 := rfl

@[simp]
theorem localTWeight_Y (j : Fin d) : localTWeight d (localY j) = 0 := rfl

/-- The `T`-weight of an exponent is its `T` exponent. -/
theorem weight_localTWeight (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localTWeight d) e = e (localT d) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_option]
  simp [localTWeight, localT]

end ReedSolomon.HiddenDerivative

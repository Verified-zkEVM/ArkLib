/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.InterpolationSpace
import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Local variables and weights for hidden-derivative interpolation

This file names the variables used after translating a differential polynomial to an agreement
point.  The shared auxiliary slot is called `U` before the hidden-derivative rewrite and `E`
afterward:

* `localT d` is the displacement variable `T`;
* `localU d = localE d` is the auxiliary/error slot;
* `localY j` represents the visible jet variable `Y_(j+1)`.

The contact weight of `T^i E^b` is `i + d*b`.  The local anisotropic weight assigns weight `j`
to zero-based `localY j`, matching weight `(j+1)-1` on the paper variable `Y_(j+1)`.

The definitions rework the sound algebraic part of ArkLib commits `1b827589`, `71214c68`, and
`d3370654`.  They deliberately use the donor-compatible `JetVariable` API from
`HiddenDerivative.InterpolationSpace`, rather than reintroducing the incompatible inductive
global-variable type from that earlier stack.  No theorem from the proof-hole-bearing merge
commits `3feac154` or `07cf41c1` is used.

## References

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d : ℕ}

/-- Variables in a local expansion. `none` denotes `T`, `some none` denotes the shared
auxiliary slot, and `some (some j)` denotes `Y_(j+1)`. -/
abbrev LocalVariable (d : ℕ) := Option (Option (Fin d))

/-- Polynomials in `T`, one auxiliary variable, and `Y₁, ..., Y_d`. -/
abbrev LocalPolynomial (R : Type*) [CommSemiring R] (d : ℕ) :=
  MvPolynomial (LocalVariable d) R

/-- The local displacement variable `T`. -/
def localT (d : ℕ) : LocalVariable d := none

/-- The shared local auxiliary slot. -/
def localAux (d : ℕ) : LocalVariable d := some none

/-- The auxiliary variable before rewriting it in terms of the hidden error. -/
abbrev localU (d : ℕ) : LocalVariable d := localAux d

/-- The hidden error variable after the auxiliary rewrite. -/
abbrev localE (d : ℕ) : LocalVariable d := localAux d

/-- The local variable representing the paper variable `Y_(j+1)`. -/
def localY {d : ℕ} (j : Fin d) : LocalVariable d := some (some j)

/-- Contact weights: `T` has weight one, `E` has weight `d`, and visible jets have weight zero. -/
def localContactWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some none => d
  | some (some _) => 0

@[simp]
theorem localContactWeight_T (d : ℕ) : localContactWeight d (localT d) = 1 := rfl

@[simp]
theorem localContactWeight_U (d : ℕ) : localContactWeight d (localU d) = d := rfl

@[simp]
theorem localContactWeight_E (d : ℕ) : localContactWeight d (localE d) = d := rfl

@[simp]
theorem localContactWeight_Y (j : Fin d) : localContactWeight d (localY j) = 0 := rfl

/-- The contact order of a local monomial.  For `T^i E^b Y^e`, this is `i + d*b`. -/
def localContactOrder (d : ℕ) (e : LocalVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (localContactWeight d) e

/-- Weight detecting only the degree in the local displacement variable `T`. -/
def localTWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some _ => 0

@[simp]
theorem localTWeight_T (d : ℕ) : localTWeight d (localT d) = 1 := rfl

@[simp]
theorem localTWeight_U (d : ℕ) : localTWeight d (localU d) = 0 := rfl

@[simp]
theorem localTWeight_E (d : ℕ) : localTWeight d (localE d) = 0 := rfl

@[simp]
theorem localTWeight_Y (j : Fin d) : localTWeight d (localY j) = 0 := rfl

/-- Local form of the anisotropic higher-jet weight: `Y_(j+1)` has weight `j`; all other
variables have weight zero. -/
def localHigherJetWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => j
  | _ => 0

@[simp]
theorem localHigherJetWeight_T (d : ℕ) : localHigherJetWeight d (localT d) = 0 := rfl

@[simp]
theorem localHigherJetWeight_E (d : ℕ) : localHigherJetWeight d (localE d) = 0 := rfl

@[simp]
theorem localHigherJetWeight_Y (j : Fin d) : localHigherJetWeight d (localY j) = j := rfl

/-- Pointwise anisotropic weight on global jet variables.  `X`, `Y₀`, and `Y₁` have weight
zero, while `Y_j` has weight `j-1`. -/
def jetHigherWeight {d : ℕ} : JetVariable d → ℕ
  | none => 0
  | some j => j - 1

@[simp]
theorem jetHigherWeight_X : jetHigherWeight (d := d) none = 0 := rfl

@[simp]
theorem jetHigherWeight_Y (j : Fin (d + 1)) : jetHigherWeight (some j) = j - 1 := rfl

/-- Natural source caps for the local substitutions: `X` has cap one, `Y₀` has cap `d+1`,
and every positive-order jet has cap zero. -/
def localSubstitutionSourceWeight (d : ℕ) : JetVariable d → ℕ
  | none => 1
  | some j => Fin.cases (d + 1) (fun _ => 0) j

@[simp]
theorem localSubstitutionSourceWeight_X (d : ℕ) :
    localSubstitutionSourceWeight d none = 1 := rfl

@[simp]
theorem localSubstitutionSourceWeight_Y_zero (d : ℕ) :
    localSubstitutionSourceWeight d (some 0) = d + 1 := rfl

@[simp]
theorem localSubstitutionSourceWeight_Y_succ (j : Fin d) :
    localSubstitutionSourceWeight d (some j.succ) = 0 := by
  simp [localSubstitutionSourceWeight]

/-! ### Boundary canaries -/

/-- At order zero the auxiliary variable has contact weight zero.  This is intentional: the
order-zero interpolation argument must not infer finite dimensionality from this weight alone. -/
theorem localContactWeight_order_zero_canary :
    localContactWeight 0 (localE 0) = 0 := rfl

/-- At derivative order two, the zero-based local indices give weights zero and one to `Y₁`
and `Y₂`, respectively. -/
theorem localHigherJetWeight_order_two_canary :
    localHigherJetWeight 2 (localY (0 : Fin 2)) = 0 ∧
      localHigherJetWeight 2 (localY (1 : Fin 2)) = 1 := by
  decide

/-- At derivative order two, `T * E²` has contact order `1 + 2*2 = 5`. -/
theorem localContactOrder_order_two_canary :
    let e : LocalVariable 2 →₀ ℕ :=
      Finsupp.single (localT 2) 1 + Finsupp.single (localE 2) 2
    localContactOrder 2 e = 5 := by
  simp [localContactOrder, Finsupp.weight_single]

end ReedSolomon.HiddenDerivative

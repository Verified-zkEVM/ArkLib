/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import Mathlib.Algebra.Polynomial.Roots

/-!
# Evaluation through a ring embedding, and the interpolation kernel

The univariate leg of the claim-transport layer (see the folder umbrella
`ArkLib/ProofSystem/RingSwitching/Transport.lean`): move a polynomial identity with
coefficients in a base ring `R` into a target carrier `F`, check it there at points, and
recover the original identity from agreement at enough points.

* `evalAt φF a : R[X] →+* F` — evaluation of a base-ring polynomial at a carrier point `a`
  through the ring homomorphism `φF : R →+* F`, bundled as a ring homomorphism so transported
  identities follow from `map_add`/`map_mul`: any polynomial identity over `R[X]` holds under
  `evalAt φF a` for every `a`.
* `eq_of_evalAt_eq` — the **interpolation kernel**, the converse direction and the reason
  point-checking a transported identity is sound: two polynomials of `natDegree < N` that
  agree under `evalAt` at `N` pairwise-distinct points of a domain are equal.

Together they turn "an `R[X]`-identity of bounded degree" into "finitely many equations in
`F`" and back — the mechanism by which a reduction hands a base-ring claim to a carrier that
only ever sees evaluations (e.g. at verifier challenges).

The multivariate leg — coefficient-wise transport of degree-bounded polynomials — is the
sibling file `Coeffs.lean`. In this folder, `Lift`
(`RingSwitching/Lift/`) consumes both directions of this file: `evalAt` to state its
challenge-local checks, `eq_of_evalAt_eq` to extract from sufficiently many accepted
challenges.
-/

open Polynomial

namespace RingSwitching

section EvalAt

variable {R : Type*} [CommSemiring R]

/-- Evaluation of a base-ring polynomial at a point `a` of a target carrier `F`, through the
ring homomorphism `φF : R →+* F` — bundled as a ring homomorphism `R[X] →+* F`, so that
transported identities follow from `map_add`/`map_mul`. -/
noncomputable def evalAt {F : Type*} [CommSemiring F] (φF : R →+* F) (a : F) :
    Polynomial R →+* F :=
  Polynomial.eval₂RingHom φF a

/-- `evalAt` computes as evaluation of the coefficient-mapped polynomial. -/
theorem evalAt_apply {F : Type*} [CommSemiring F] (φF : R →+* F) (a : F) (p : Polynomial R) :
    evalAt φF a p = (p.map φF).eval a := by
  simp [evalAt, Polynomial.eval₂_eq_eval_map]

end EvalAt

/-- **Interpolation kernel**: two polynomials of `natDegree < N` that agree under `evalAt` at
`N` pairwise-distinct points of a domain are equal — the defect polynomial has more roots
than its degree, so it vanishes, and injectivity of `φF` reflects equality back to `R[X]`.
This is what makes point-checking a transported polynomial identity sound: `N` accepted
evaluations pin down a degree-`< N` object exactly. -/
theorem eq_of_evalAt_eq {R : Type*} [CommRing R] {F : Type*} [CommRing F] [IsDomain F]
    {φF : R →+* F} (hφF : Function.Injective φF) {N : ℕ}
    {S T : Polynomial R} (hS : S.natDegree < N) (hT : T.natDegree < N)
    {A : Fin N → F} (hA : Function.Injective A)
    (h : ∀ j, evalAt φF (A j) S = evalAt φF (A j) T) : S = T := by
  have hzero : (S - T).map φF = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hA (fun j => ?_) ?_
    · have hj := h j
      rw [evalAt_apply, evalAt_apply] at hj
      rw [Polynomial.map_sub, Polynomial.eval_sub, hj, sub_self]
    · rw [Fintype.card_fin]
      have h1 : ((S - T).map φF).natDegree ≤ (S - T).natDegree :=
        Polynomial.natDegree_map_le
      have h2 := Polynomial.natDegree_sub_le S T
      omega
  have hST : S - T = 0 := by
    apply Polynomial.map_injective φF hφF
    rw [hzero, Polynomial.map_zero]
  exact sub_eq_zero.mp hST

end RingSwitching

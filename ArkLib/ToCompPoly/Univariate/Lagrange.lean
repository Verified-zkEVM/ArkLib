/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompPoly.Univariate.Lagrange

/-!
  # Additions to `CompPoly.Univariate.Lagrange` not yet upstreamed to CompPoly.
-/

namespace CompPoly.CPolynomial.CLagrange

variable {R ι : Type*} [BEq R] [Field R] [LawfulBEq R] [DecidableEq ι]

lemma interpolation_of_constants (s : Finset ι) (x y : ι → R) (c : R)
    (hy : ∀ i ∈ s, y i = c) (hx : Set.InjOn x s) (hs : s.Nonempty) :
    interpolate s x y = CPolynomial.C c := by
  suffices h : (interpolate s x y).toPoly = (CPolynomial.C c).toPoly from
    CPolynomial.ringEquiv.injective h
  rw [cinterpolate_eq_interpolate, CPolynomial.C_toPoly]
  symm
  exact Lagrange.eq_interpolate_of_eval_eq y hx
    (lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Finset.card_pos.mpr hs))
    (fun i hi => by simp [hy i hi])

end CompPoly.CPolynomial.CLagrange

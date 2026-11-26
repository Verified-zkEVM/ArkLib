/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.ToCompPoly.Univariate.DegreeLT
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance cases for bounded computable polynomials -/

open CompPoly

-- The search over computable polynomials of degree at most one finds `X` over `𝔽₅`.
example : ∃ p : ↥(CPolynomial.degreeLT (R := ZMod 5) (1 + 1)),
    p.val.toPoly = Polynomial.X :=
  (CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le 1 (· = Polynomial.X)
    fun _ hp ↦ hp ▸ Polynomial.degree_X_le).mpr ⟨_, rfl⟩

-- Every element of `degreeLT 3` converts to a polynomial of degree at most two.
example (p : ↥(CPolynomial.degreeLT (R := ZMod 5) (2 + 1))) : p.val.toPoly.degree ≤ 2 :=
  CPolynomial.degree_toPoly_le p

/-- info: 'CompPoly.CPolynomial.degree_toPoly_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.CPolynomial.degree_toPoly_le

/-- info: 'CompPoly.CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le

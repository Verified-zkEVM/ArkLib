/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Univariate.Basic

/-!
# Finite rational univariate representation data

A raw map describes coordinates `N_i(U)/B(U)` at roots of an eliminant `h(U)`. The data contains
no root list or correctness certificate. `Postprocess` removes forbidden roots, enforces zero
equations, and produces reduced polynomial coordinates; `FromRaw` first normalizes a possibly
repeated or inseparable eliminant. Keeping these containers here lets solver construction depend
only on their representation, independently of the postprocessor proofs.
-/

@[expose] public section

namespace ArkLib.UnivariateRepresentation
open CompPoly
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Polynomial data returned by an upstream rational-univariate-map solver. -/
structure MapData where
  modulus : CPolynomial F
  denominator : CPolynomial F
  numerators : List (CPolynomial F)

/-- A polynomial representation after denominator and equation filtering. -/
structure Representation where
  modulus : CPolynomial F
  coordinates : List (CPolynomial F)

end ArkLib.UnivariateRepresentation

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CompPoly.Univariate.Basic

/-!
  # Additions to `CompPoly.Univariate.Basic` not yet upstreamed to CompPoly.
-/

namespace CompPoly.CPolynomial

variable {R : Type*}

/-- Construct a canonical polynomial from a coefficient function `Fin n → R`.

  The coefficients are stored in an array (index `i` gives the coefficient of `X^i`)
  and then trimmed to remove trailing zeros.
-/
def ofFn [Zero R] [BEq R] [LawfulBEq R] {n : ℕ} (f : Fin n → R) : CPolynomial R :=
  ⟨(Raw.mk (Array.ofFn f)).trim, Raw.Trim.isCanonical_trim _⟩

end CompPoly.CPolynomial

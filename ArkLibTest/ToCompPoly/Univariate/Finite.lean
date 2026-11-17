/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ToCompPoly.Univariate.Finite
import Mathlib.Algebra.Field.ZMod

/-! # Runtime checks for bounded polynomial enumeration -/

open CompPoly

-- A zero-length coefficient vector represents exactly the zero polynomial.
/-- info: 1 -/
#guard_msgs in
#eval Fintype.card ↥(CPolynomial.degreeLT (R := ZMod 2) 0)

/-- info: 4 -/
#guard_msgs in
#eval Fintype.card ↥(CPolynomial.degreeLT (R := ZMod 2) 2)

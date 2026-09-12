/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.NonvanishingGrid

/-! Rejected early points, deterministic ordering, constants, and dimension-zero search. -/

open CPoly CPoly.CMvPolynomial CPoly.NonvanishingGrid

namespace NonvanishingGridTests

/-- The prefix-size theorem applies to a concrete nonconstant polynomial. -/
example : ∃ x, selectNonzero (X 0 : CMvPolynomial 2 ℤ) [0, 1] = some x := by
  apply selectNonzero_exists_of_nodup
  · intro h
    have he := congrArg (fun p : CMvPolynomial 2 ℤ => p.eval (fun _ => 1)) h
    simp at he
  · decide
  · simp [CMvPolynomial.fromCMvPolynomial_X]

/-- Run the actual Cartesian search, including degenerate grid shapes. -/
def run : IO Unit := do
  let p : CMvPolynomial 2 ℤ := X 0
  let found := (selectNonzero p [0, 1]).map fun x => [x 0, x 1]
  unless found == some [1, 0] do
    throw (IO.userError "grid search did not reject early zeros in lexicographic order")
  unless (selectNonzero p [0, 0, 1]).map (fun x => [x 0, x 1]) == some [1, 0] do
    throw (IO.userError "duplicate scalar values changed first nonzero point")
  unless (selectNonzero (p * (p - 1)) [0, 0, 1]).isNone do
    throw (IO.userError "repeated scalars incorrectly supplied extra distinct grid points")
  unless (selectNonzero (0 : CMvPolynomial 2 ℤ) [0, 1]).isNone do
    throw (IO.userError "zero polynomial produced a nonvanishing point")
  unless (selectNonzero (C 3 : CMvPolynomial 2 ℤ) []).isNone do
    throw (IO.userError "positive-dimensional empty grid produced a point")
  unless (selectNonzero (C 3 : CMvPolynomial 2 ℤ) [0]).isSome do
    throw (IO.userError "nonzero constant failed on a singleton scalar grid")
  unless (selectNonzero (C 3 : CMvPolynomial 0 ℤ) []).isSome do
    throw (IO.userError "dimension-zero grid lost its unique point")
  unless (selectNonzero (0 : CMvPolynomial 0 ℤ) []).isNone do
    throw (IO.userError "zero constant passed dimension-zero search")

end NonvanishingGridTests

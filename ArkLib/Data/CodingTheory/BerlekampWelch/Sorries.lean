/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Matrix.Mul

/-!
  # All the sorries Berlekamp-Welch decoder relies upon.

  The sorries are related to solving linear systems of equations.
-/

variable {α : Type} {F : Type} [Field F]
variable {n m : ℕ}

/--
Opaque linear system solver for Berlekamp-Welch decoding.

Solves the matrix equation A·x = b for x, where:
- A is an n × m coefficient matrix
- b is a length-n RHS vector
Returning either:
- `some x` if a solution exists
- `none` if the system is inconsistent

### Parameters:
- `A : Matrix (Fin n) (Fin m) F` - Coefficient matrix with dimensions n × m
- `b : Fin n → F` - Right-hand side vector of length n

### Returns:
- `some x` where `x : Fin m → F` is a solution vector if one exists
- `none` if the system has no solution

### Behavior:
1. For consistent systems (solutions exist):
   - Returns any valid solution
2. For inconsistent systems (no solution):
   - Returns `none`

### Implementation Notes:
- Marked `opaque` because:
  - There is no means currently to provide the definition using Mathlib (`sorry` under the hood).
- Used internally by the Berlekamp-Welch decoder
-/
opaque linsolve (A : Matrix (Fin n) (Fin m) F) (b : Fin n → F) : Option (Fin m → F)
  := sorry

/--
**Solution correctness theorem** for the linear system solver.

### Theorem Statement:
If `linsolve` returns `some x`, then `x` is indeed a solution to the linear system.

### Parameters:
- `A : Matrix (Fin n) (Fin m) F` - Coefficient matrix
- `b : Fin n → F` - Right-hand side vector
- `x : Fin m → F` - Candidate solution vector
- `h : linsolve A b = some x` - Proof that the solver returned this solution
-/
theorem linsolve_some {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F} {x : Fin m → F}
  (h : linsolve A b = some x)
  : A.mulVec x = b := sorry

/--
**Inconsistency theorem** for the linear system solver.

### Theorem Statement:
If `linsolve` returns `none`, the linear system has no solution.

### Parameters:
- `A : Matrix (Fin n) (Fin m) F` - Coefficient matrix
- `b : Fin n → F` - Right-hand side vector
- `h : linsolve A b = none` - Proof that the solver failed to find a solution
-/
theorem linsolve_none {A : Matrix (Fin n) (Fin m) F} {b : Fin n → F}
  (h : linsolve A b = none)
  : ¬∃ x, A.mulVec x = b := by sorry

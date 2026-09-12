/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.BoxTruncation

/-! Executable box arithmetic regressions over a semiring, without a field instance. -/

open CPoly

namespace BoxTruncationTests

private def eps₀ : CMvPolynomial 2 ℕ := CMvPolynomial.monomial #m[1, 0] 1
private def eps₁ : CMvPolynomial 2 ℕ := CMvPolynomial.monomial #m[0, 1] 1
private def constant : CMvPolynomial 2 ℕ := CMvPolynomial.monomial #m[0, 0] 7

/-- Kernel-checked use of the production associativity theorem. -/
example (p q s : CMvPolynomial 2 ℕ) :
    BoxTruncation.mul 2 (BoxTruncation.mul 2 p q) s =
      BoxTruncation.mul 2 p (BoxTruncation.mul 2 q s) :=
  BoxTruncation.mul_assoc 2 p q s

/-- Execute concrete regressions for coordinatewise, rather than total-degree, precision. -/
def run : IO Unit := do
  -- Precision one retains constants and discards both parameter directions.
  unless (BoxTruncation.truncate 1 (constant + eps₀ + eps₁)).coeff #m[0, 0] = 7 do
    throw (IO.userError "precision one lost constant")
  unless (BoxTruncation.truncate 1 (constant + eps₀ + eps₁)).coeff #m[1, 0] = 0 do
    throw (IO.userError "precision one retained first parameter")
  unless (BoxTruncation.truncate 1 (constant + eps₀ + eps₁)).coeff #m[0, 1] = 0 do
    throw (IO.userError "precision one retained second parameter")
  -- A mixed term of total degree two must survive precision two.
  unless (BoxTruncation.mul 2 eps₀ eps₁).coeff #m[1, 1] = 1 do
    throw (IO.userError "precision two lost mixed term")
  -- A square overflows one coordinate even though the mixed term survives.
  unless (BoxTruncation.mul 2 eps₀ eps₀).coeff #m[2, 0] = 0 do
    throw (IO.userError "precision two retained square")
  -- This distinguishes the box operation from total-degree truncation below two.
  unless (CMvPolynomial.restrictTotalDegree 1 (eps₀ * eps₁)).coeff #m[1, 1] = 0 do
    throw (IO.userError "total degree comparison failed")
  unless (BoxTruncation.add 2 (eps₀ * eps₁) (eps₀ * eps₁)).coeff #m[1, 1] = 2 do
    throw (IO.userError "truncated addition lost multiplicity")
  -- Precision zero discards constants when there is at least one parameter.
  unless (BoxTruncation.truncate 0 constant).coeff #m[0, 0] = 0 do
    throw (IO.userError "precision zero retained constant with parameters")
  -- With no parameters, the empty box condition is vacuous even at precision zero.
  let c : CMvPolynomial 0 ℕ := CMvPolynomial.monomial #m[] 7
  unless (BoxTruncation.truncate 0 c).coeff #m[] = 7 do
    throw (IO.userError "empty parameter set lost constant")


end BoxTruncationTests

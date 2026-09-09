/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintKernel
import Mathlib.Data.ZMod.Basic
/-!
# Boundary canary for the exhibited local-constraint kernel

The generic kernel theorem says that contact order at least `m` is discarded.  This concrete
counter-boundary checks that contact order `3` is retained when `m = 5`; it would fail if the
strict projection boundary, the error weight, or the triangular rewrite were implemented in the
wrong direction.
-/

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

/-- `T (E♯)` is not killed at multiplicity five when the derivative order is two. -/
theorem belowContactThreshold_not_in_kernel_canary :
    enlargedLocalConstraintMap (R := ZMod 5) (d := 2) 5
      (exhibitedKernelFactor 2 1 1) ≠ 0 := by
  intro h
  rw [enlargedLocalConstraintMap, LinearMap.comp_apply] at h
  change projectLowContact (R := ZMod 5) (d := 2) 5
    (rewriteUToE 2 (exhibitedKernelFactor 2 1 1)) = 0 at h
  rw [rewriteUToE_exhibitedKernelFactor, T_pow_mul_E_pow_eq_monomial] at h
  have hc := congrArg (MvPolynomial.coeff (contactKernelExponent 2 1 1)) h
  simp only [projectLowContact, coeff_filterLocalMonomials,
    localContactOrder_contactKernelExponent, mul_one, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, coeff_monomial, coeff_zero] at hc
  exact (by decide : (1 : ZMod 5) ≠ 0) hc

end ReedSolomon.HiddenDerivative

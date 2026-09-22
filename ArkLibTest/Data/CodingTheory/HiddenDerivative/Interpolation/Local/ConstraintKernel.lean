/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintKernel

/-!
# Exhibited kernel acceptance tests

An instance of the kernel membership at the contact order `m = r + d h`, and the failure of
membership one step past it, which is why `exhibitedKernelMultiplier_mem_ker` needs
`m ≤ r + d h`. Injectivity is instantiated over `ℤ`, a domain that is not a field.
-/

open MvPolynomial ReedSolomon.HiddenDerivative

/-- `d = 2, r = 1, h = 1`: the factor `T (U - localJetSum 2)` has contact order `3`. -/
example (G : LocalPolynomial ℚ 2) :
    exhibitedKernelMultiplier 2 1 1 G ∈ LinearMap.ker (enlargedLocalConstraintMap (d := 2) 3) :=
  exhibitedKernelMultiplier_mem_ker (by norm_num) G

/-- `d = 1, r = 0, h = 0, m = 1`: the factor is `1`, of contact order `0 < 1`, and the enlarged
map does not kill it. -/
example : exhibitedKernelMultiplier (R := ℚ) 1 0 0 1 ∉
    LinearMap.ker (enlargedLocalConstraintMap (d := 1) 1) := by
  intro h
  have hc := congrArg (fun p : LocalPolynomial ℚ 1 => p.coeff 0) (LinearMap.mem_ker.mp h)
  simp [enlargedLocalConstraintMap, exhibitedKernelFactor, localContactOrder] at hc

/-- Multiplication by the exhibited factor is injective over `ℤ`. -/
example : Function.Injective (exhibitedKernelMultiplier (R := ℤ) 3 2 1) :=
  exhibitedKernelMultiplier_injective 3 2 1

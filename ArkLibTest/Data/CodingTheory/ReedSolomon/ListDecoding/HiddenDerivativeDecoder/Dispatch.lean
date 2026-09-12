/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeDecoder.Correctness
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance checks for the paper decoder dispatch

These checks force the impossible-agreement, constant, bounded-fallback, and symbolic branches.
The last case confirms that a symbolic failure is observable and does not silently execute the
subset decoder.
-/

open _root_.ReedSolomon.ListDecoding.HiddenDerivativeDecoder

namespace ArkLibTest.ReedSolomon.ListDecoding.HiddenDerivativeDecoder

local instance primeTwentyThree : Fact (Nat.Prime 23) := ⟨by decide⟩

private def cmpZMod23 : ZMod 23 → ZMod 23 → Ordering := fun a b ↦ compare a.val b.val

private instance : Std.TransCmp cmpZMod23 where
  eq_swap := by
    intro a b
    exact Std.OrientedCmp.eq_swap (cmp := compare) (a := a.val) (b := b.val)
  isLE_trans := by
    intro a b c hab hbc
    exact Std.TransCmp.isLE_trans (cmp := compare) hab hbc

private instance : Std.LawfulEqCmp cmpZMod23 where
  eq_of_compare := by
    intro a b hab
    apply ZMod.val_injective
    exact Std.LawfulEqCmp.eq_of_compare (cmp := compare) hab

private def input : Input (ZMod 23) 10 where
  domain := ⟨fun i ↦ i.val, by
    intro a b hab
    apply Fin.ext
    have hvals := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt (by omega : (a : Nat) < 23),
      ZMod.val_natCast_of_lt (by omega : (b : Nat) < 23)] using hvals⟩
  received := fun _ ↦ 0
  k := 2
  agreement := 2
  characteristic := 23

private def options : Options where
  order := 1
  multiplicity := 1
  jetDegree := 2
  xDegreeFactor := 1

private def equation : SuppliedEquation (ZMod 23) options where
  polynomial := CPoly.CMvPolynomial.C 1

private def zeroEquation : SuppliedEquation (ZMod 23) options where
  polynomial := 0

private def malformedCertificate : SupportCertificate where
  vectors := []

/-- The first branch has priority. -/
example : dispatch (F := ZMod 23) ({ input with agreement := 11 }) options =
    .impossibleAgreement := by decide

/-- A constant message uses frequency counting. -/
example : dispatch (F := ZMod 23) ({ input with k := 1 }) options = .constant := by decide

/-- `k <= d` forces the bounded subset fallback. -/
example : dispatch (F := ZMod 23) ({ input with k := 1 + 1 })
    ({ options with order := 2 }) = .boundedFallback := by decide

/-- A large guarded input reaches the symbolic branch. -/
example : dispatch (F := ZMod 23) input options = .symbolic := by decide

/-- Symbolic construction failure is explicit and does not fall back. -/
example : runSupplied cmpZMod23 input options equation =
    .error .symbolicBackendUnavailable := by decide

/-- A zero supplied equation is rejected before symbolic execution. -/
example : runSupplied cmpZMod23 input options zeroEquation =
    .error .invalidEquation := by decide

/-- Early branches have priority over malformed interpolation support. -/
example : runCertified cmpZMod23 ({ input with agreement := 11 }) options
    malformedCertificate = .ok [] := by decide

/-- The constant branch also runs before interpolation support is inspected. -/
example : runCertified cmpZMod23 ({ input with k := 1 }) options malformedCertificate =
    runSupplied cmpZMod23 ({ input with k := 1 }) options equation := by decide

/-- The bounded fallback also runs before interpolation support is inspected. -/
example : runCertified cmpZMod23 input ({ options with order := 2 }) malformedCertificate =
    runSupplied cmpZMod23 input ({ options with order := 2 })
      ({ polynomial := CPoly.CMvPolynomial.C 1 } :
        SuppliedEquation (ZMod 23) { options with order := 2 }) := by
  have hb : dispatch input { options with order := 2 } = .boundedFallback := by decide
  simp [runCertified, runSupplied, hb]

/-- Certificate failure remains observable once the symbolic branch is reached. -/
example : runCertified cmpZMod23 input options malformedCertificate =
    .error .certificateFailure := by decide

end ArkLibTest.ReedSolomon.ListDecoding.HiddenDerivativeDecoder

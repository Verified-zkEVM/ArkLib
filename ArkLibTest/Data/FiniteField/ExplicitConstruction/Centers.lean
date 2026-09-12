/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.Centers

/-! Executed Euler-search and short quadratic-center-prefix checks. -/

namespace ExplicitCenterTests

open ArkLib.FiniteField.ExplicitConstruction ArkLib.FiniteFieldCandidates

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2) :
    ¬IsSquare (certifiedNonsquare p hodd).val := (certifiedNonsquare p hodd).property

example (p : ℕ) [Fact p.Prime] (a : ZMod p) (count : ℕ) (h : count ≤ p ^ 2) :
    (quadraticPrefix p a count).Nodup := nodup_quadraticPrefix p a count h

/-- Check first-success search, unsupported characteristic, exact prefix length, and a
quadratic prefix crossing the prime-field cardinality without materializing its full alphabet. -/
def run : IO Unit := do
  unless nonsquareParameter? 3 == some (2 : ZMod 3) do
    throw (IO.userError "Euler search did not reject zero/one and choose two over F3")
  unless nonsquareParameter? 5 == some (2 : ZMod 5) do
    throw (IO.userError "Euler search selected the wrong first nonsquare over F5")
  unless nonsquareParameter? 7 == some (3 : ZMod 7) do
    throw (IO.userError "Euler search failed to reject the square two over F7")
  unless (nonsquareParameter? 2).isNone do
    throw (IO.userError "Euler search fabricated a nonsquare in characteristic two")
  let parameter := certifiedNonsquare 5 (by decide)
  unless parameter.val == (2 : ZMod 5) do
    throw (IO.userError "certification changed the executed parameter")
  let centers := quadraticPrefix 5 parameter.val 7
  unless centers.length == 7 do
    throw (IO.userError "quadratic prefix did not allocate exactly seven centers")
  unless decide centers.Nodup do
    throw (IO.userError "quadratic prefix contains duplicates")
  unless (centers[5]?).map QuadraticAlgebra.re == some (0 : ZMod 5) &&
      (centers[5]?).map QuadraticAlgebra.im == some (1 : ZMod 5) do
    throw (IO.userError "quadratic prefix failed to cross the prime-field boundary")
  unless (quadraticPrefix 5 parameter.val 0).isEmpty do
    throw (IO.userError "zero-size prefix allocated entries")
  unless (quadraticPrefix 5 parameter.val 25).length == 25 do
    throw (IO.userError "quadratic prefix failed at its exact cardinality boundary")
  let fieldCheck : Bool :=
    letI := QuadraticAlgebra.fieldOfNonsquare parameter.val parameter.property
    let w : QuadraticAlgebra (ZMod 5) parameter.val 0 := ⟨0, 1⟩
    decide (w * w = ⟨parameter.val, 0⟩ ∧ (w + 1) * (w + 1)⁻¹ = 1)
  unless fieldCheck do
    throw (IO.userError "computed quadratic-field arithmetic/inverse failed")
  unless (primeFieldPrefix (ZMod 5) 3).length == 3 do
    throw (IO.userError "existing prime-field prefix failed")

#print axioms ArkLib.FiniteField.ExplicitConstruction.nonsquareParameter?_ne_none
#print axioms ArkLib.FiniteField.ExplicitConstruction.certifiedNonsquare_execution
#print axioms ArkLib.FiniteField.ExplicitConstruction.nodup_quadraticPrefix

end ExplicitCenterTests

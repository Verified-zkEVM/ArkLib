/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.TreeRefinement
import Mathlib.FieldTheory.Finite.Basic

/-! Crossed strata exercise every branch of a three-leaf recursive factor tree. -/

namespace FullSquarefreeTreeTests

open CompPoly CompPoly.CPolynomial
open CompPoly.CPolynomial.FullSquarefreeDecomposition

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Each of two residue strata meets all three recursive leaves. -/
def run : IO Unit := do
  let x : CPolynomial (ZMod 7) := X
  let q₁ := x * (x - 1)
  let q₂ := (x - 2) * (x - 3)
  let q₃ := (x - 4) * (x - 5)
  let h₁ := x * (x - 2) * (x - 4)
  let h₂ := (x - 1) * (x - 3) * (x - 5)
  let M := MulContext.naive (R := ZMod 7)
  let D := ModContext.naive (R := ZMod 7)
  let [tree] := BatchRemainder.build M [q₁, q₂, q₃]
    | throw (IO.userError "balanced tree builder did not return one root")
  unless tree.product == q₁ * q₂ * q₃ do
    throw (IO.userError "recursive factor tree product is incorrect")
  let routed := route M D tree [h₁, h₂]
  unless routed == [(q₁, x), (q₁, x - 1), (q₂, x - 2), (q₂, x - 3),
      (q₃, x - 4), (q₃, x - 5)] do
    throw (IO.userError "crossed residue pieces reached incorrect recursive leaves")
  let tagged := routeTagged M D tree [(1, h₁), (2, h₂)]
  unless tagged == [(1, q₁, x), (2, q₁, x - 1), (1, q₂, x - 2),
      (2, q₂, x - 3), (1, q₃, x - 4), (2, q₃, x - 5)] do
    throw (IO.userError "batched tree route lost origin residue labels")
  let refined := refineRoot M D tree [(1, h₁ * (x - 6)), (2, h₂)]
  unless refined.1 == tagged && refined.2 == [(1, x - 6)] do
    throw (IO.userError "initial root split lost the residue-only factor or its label")
  unless (refined.1.map (fun z => z.2.2)).prod * (refined.2.map Prod.snd).prod ==
      h₁ * (x - 6) * h₂ do
    throw (IO.userError "initial batch and routed intersections do not reconstruct input")
  unless (routed.map Prod.snd).prod == h₁ * h₂ do
    throw (IO.userError "tree routing lost part of a residue stratum")
  unless weightedProduct M [(1, h₁), (2, h₂), (3, x - 6)] ==
      h₁ * h₂ ^ 2 * (x - 6) ^ 3 do
    throw (IO.userError "balanced weighted stratum product is incorrect")
  unless weightedProduct M ([] : List (ℕ × CPolynomial (ZMod 7))) == 1 do
    throw (IO.userError "empty weighted product is not one")
  unless route M D tree [x, 1] == [(q₁, x)] do
    throw (IO.userError "unit pieces propagated into unrelated recursive leaves")
  unless route M D tree [] == [] do
    throw (IO.userError "empty routing produced a factor")

end FullSquarefreeTreeTests

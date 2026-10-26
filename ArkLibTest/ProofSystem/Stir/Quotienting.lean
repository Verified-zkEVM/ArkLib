/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.FieldTheory.Finite.Basic
import ArkLib.ProofSystem.Stir.Quotienting

/-!
# STIR quotienting: the evaluation points are those of the code's domain

`funcQuotient` and `disagreementSet` evaluate `Ans'` and `V_S` at `domain x`, the points of the
domain of `ReedSolomon.code domain`. For the inclusion of a finite set of points this is the
textbook formula in `x`; for another injective domain it is not, which is the case the previous
statement of `quotienting` got wrong (#1262).
-/

open Polynomial Quotienting

namespace ArkLibTest.StirQuotienting

/-- For the inclusion of a finite set of points, the quotient is the textbook formula in `x`. -/
example {F : Type*} [Field F] [DecidableEq F] (L : Finset F) (f : ↥L → F) (S : Finset F)
    (Ans Fill : S → F) (x : ↥L) :
    funcQuotient (Function.Embedding.subtype (· ∈ L)) f S Ans Fill x =
      if hx : (x : F) ∈ S then Fill ⟨x, hx⟩
      else (f x - (ansPoly S Ans).eval (x : F)) / (vanishingPoly S).eval (x : F) :=
  rfl

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Over `ZMod 5` the map `x ↦ x ^ 3` is a permutation. -/
private def cube : ZMod 5 ↪ ZMod 5 := ⟨fun x => x ^ 3, by decide⟩

/-- For the permutation domain `x ↦ x ^ 3`, the quotient of `f x = x` by `S = {0}` is
`x / x ^ 3`, not the constant `1` that evaluating at the points `x` themselves would give. -/
example : funcQuotient cube (fun x : ZMod 5 => x) ({0} : Finset (ZMod 5))
    (fun _ => 0) (fun _ => 1) 2 = 4 := by
  have h0 : ansPoly ({0} : Finset (ZMod 5)) (fun _ => 0) = 0 :=
    map_zero (Lagrange.interpolate ({0} : Finset (ZMod 5)).attach fun i => (i : ZMod 5))
  have hx : cube 2 ∉ ({0} : Finset (ZMod 5)) := by decide
  rw [funcQuotient_of_not_mem hx, h0]
  simp only [eval_zero, sub_zero, vanishingPoly, Finset.prod_singleton, eval_sub, eval_X, eval_C]
  decide +kernel

end ArkLibTest.StirQuotienting

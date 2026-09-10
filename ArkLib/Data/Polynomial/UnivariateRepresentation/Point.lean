/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.UnivariateRepresentation.Basic

/-!
# Point semantics for raw rational univariate maps

This neutral predicate records the exact root, denominator, width, and rational
coordinate equations supplied by a raw map.  Solver frontends and downstream
chart consumers can share it without depending on Reed--Solomon code.
-/

@[expose] public section

namespace ArkLib.UnivariateRepresentation.MapData

open CompPoly

variable {F K : Type*} [Field F] [BEq F] [LawfulBEq F] [Field K]
variable {s : ℕ}

/-- A raw rational map represents `point` at the parameter root `theta`. -/
def RepresentsPoint (input : MapData (F := F)) (ι : F →+* K)
    (theta : K) (point : Fin s → K) : Prop :=
  input.modulus.toPoly.eval₂ ι theta = 0 ∧
  input.denominator.toPoly.eval₂ ι theta ≠ 0 ∧
  input.numerators.length = s ∧
  ∀ i : Fin s,
    (input.numerators[i.val]?.getD 0).toPoly.eval₂ ι theta /
      input.denominator.toPoly.eval₂ ι theta = point i

end ArkLib.UnivariateRepresentation.MapData

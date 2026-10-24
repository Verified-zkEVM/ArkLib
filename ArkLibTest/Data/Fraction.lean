/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Fraction
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Acceptance checks for unnormalized fraction folds -/

open FractionPair

namespace FractionPair.Test

/-- An ordinary external caller of the generic fold, outside any noncomputable section. -/
def foldCaller {R : Type} [CommSemiring R] (ps : List (FractionPair R)) : FractionPair R :=
  FractionPair.sum ps

/-- An ordinary external caller of field evaluation. -/
def valueCaller {F : Type} [Field F] (p : FractionPair F) : F := p.value

example : foldCaller ([⟨1, 2⟩, ⟨3, 5⟩, ⟨4, 7⟩] : List (FractionPair ℕ)) = ⟨117, 70⟩ := by
  decide

example : foldCaller ([] : List (FractionPair ℕ)) = ⟨0, 1⟩ := by
  decide

example : foldCaller ([⟨3, 0⟩, ⟨4, 2⟩] : List (FractionPair ℕ)) = ⟨6, 0⟩ := by
  decide

/-- Equal zero blocks may carry distinct helper values, because the theorem indexes groups. -/
example {R : Type*} [CommRing R] (h : R) :
    (FractionPair.sum (([true, false].map fun _ =>
      [⟨0, 0⟩] : List (List (FractionPair R)))).flatten).numerator = 0 := by
  apply sum_flatten_numerator_eq_zero [true, false] (fun _ => [⟨0, 0⟩])
    (fun b => if b then h else -h)
  · intro b _
    simp
  · simp

abbrev F := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : valueCaller (foldCaller ([⟨1, 2⟩, ⟨3, 5⟩] : List (FractionPair F))) = 6 := by
  apply (div_eq_iff (show (foldCaller
    ([⟨1, 2⟩, ⟨3, 5⟩] : List (FractionPair F))).denominator ≠ 0 by decide)).2
  decide

/-- Total field division at zero does not turn the pair fold into unrestricted fraction addition. -/
example : valueCaller (combine (⟨1, 0⟩ : FractionPair F) ⟨1, 1⟩) = 0 ∧
    valueCaller (⟨1, 0⟩ : FractionPair F) + valueCaller ⟨1, 1⟩ = 1 := by
  simp [valueCaller, combine, value]

#eval foldCaller ([⟨1, 2⟩, ⟨3, 5⟩, ⟨4, 7⟩] : List (FractionPair ℕ))
#eval valueCaller (foldCaller ([⟨1, 2⟩, ⟨3, 5⟩] : List (FractionPair F)))
#eval (valueCaller (combine (⟨1, 0⟩ : FractionPair F) ⟨1, 1⟩),
  valueCaller (⟨1, 0⟩ : FractionPair F) + valueCaller ⟨1, 1⟩)

-- A long input exercises the runtime fold without a kernel reduction proof.
#eval let p := foldCaller (List.replicate 100000 (unit : FractionPair ℕ))
  (p.numerator, p.denominator)

open Lean Elab Command

run_cmd do
  for n in #[``FractionPair.combine, ``FractionPair.sum, ``FractionPair.map,
      ``FractionPair.value, ``foldCaller, ``valueCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) n).isSome do
      throwError "Expected compiler IR for `{n}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``FractionPair.combine_assoc, ``FractionPair.combine_comm,
      ``FractionPair.sum_append, ``FractionPair.sum_flatten, ``FractionPair.sum_eq_of_perm,
      ``FractionPair.sum_denominator,
      ``FractionPair.sum_flatten_numerator_eq_sum_mul_denominator,
      ``FractionPair.sum_flatten_numerator_eq_zero, ``FractionPair.map_sum,
      ``FractionPair.value_sum] do
    let axioms ← collectAxioms n
    unless axioms.all allowed.contains do
      throwError "`{n}` depends on unexpected axioms: {axioms}"

end FractionPair.Test

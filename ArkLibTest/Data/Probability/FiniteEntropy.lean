/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.Probability.FiniteEntropy
import Mathlib.Algebra.Field.ZMod

/-! # Finite-weight entropy acceptance tests -/

open Probability

-- The uniform weight on `Bool` is a probability weight.
example : IsProbWeight (fun _ : Bool => (1 / 2 : ℝ)) := ⟨fun _ => by norm_num, by norm_num⟩

-- Under the uniform weight on `Fin 4`, reduction mod `2` is `0` on `{0, 2}`, of weight `1 / 2`.
example : weightLaw (fun _ : Fin 4 => (1 / 4 : ℝ)) (fun x => (x.val : ZMod 2)) 0 = 1 / 2 := by
  rw [weightLaw, show Finset.univ.filter (fun x : Fin 4 => (x.val : ZMod 2) = 0) = {0, 2} by decide,
    Finset.sum_pair (by decide)]
  norm_num

-- The product weight multiplies the coordinate weights.
example : prodLaw (fun (_ : Fin 2) (x : ZMod 2) => if x = 0 then (1 / 3 : ℝ) else 2 / 3)
    ![0, 1] = 2 / 9 := by
  norm_num [prodLaw, Fin.prod_univ_two]

-- A constant variable has entropy `0`.
example : entQ 2 (fun _ : Bool => (1 / 2 : ℝ)) (fun _ => ()) = 0 := by
  norm_num [entQ, weightLaw]

-- A uniform bit has base-`2` entropy `1`.
example : entQ 2 (fun _ : ZMod 2 => (1 / 2 : ℝ)) id = 1 := by
  have h : ∀ b, weightLaw (fun _ : ZMod 2 => (1 / 2 : ℝ)) id b = 1 / 2 := fun b => by
    simp [weightLaw, Finset.filter_eq']
  simp only [entQ, h, Nat.cast_ofNat]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Real.negMulLog, one_div,
    Real.log_inv, div_eq_one_iff_eq (Real.log_pos one_lt_two).ne']
  push_cast
  ring

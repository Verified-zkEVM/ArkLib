/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Layout
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis

/-!
# Prefix and suffix packing layouts

A nonconstant two-variable source distinguishes the DP24 prefix layout from the Flock suffix
layout: fixing the packed coordinate to one leaves different retained components.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.Layout

open MvPolynomial Module
open RingSwitching.Packing.ScalarHead

/-- Rank-two packing of one Boolean coordinate, opening directly in `ZMod 5`. -/
abbrev ordinaryData : PackingData (ZMod 5) where
  P := (Fin 1 → Fin 2) → ZMod 5
  E := ZMod 5
  ιP := Fin 1 → Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Basis.singleton Unit (ZMod 5)

/-- Pack the first coordinate and retain the second. -/
abbrev prefixLayout := packedPrefixLayout ordinaryData 1 1 (Equiv.refl _)

/-- Retain the first coordinate and pack the second. -/
abbrev suffixLayout := packedSuffixLayout ordinaryData 1 1 (Equiv.refl _)

/-- The source `v₀ + 2 v₁`, asymmetric in its two coordinates. -/
def source : (ZMod 5)⦃≤ 1⦄[X Fin 2] :=
  ⟨MLE (fun v => (v 0 : ZMod 5) + 2 * (v 1 : ZMod 5)), MLE_mem_restrictDegree _⟩

/-- Fixing the first coordinate to one leaves value one at retained zero. -/
theorem prefix_component :
    eval (fun _ => (0 : ZMod 5)) (prefixLayout.components source (fun _ => 1)).val = 1 := by
  change eval (fun _ => (0 : ZMod 5)) (splitFirst 1 1 source (fun _ => 1)).val = 1
  have hs := splitFirst_eval 1 1 source (fun _ => 1) (fun _ => 0)
  have hp := congrArg (fun r => eval r source.val)
    ((Fin.append_comp (a := fun _ : Fin 1 => (1 : Fin 2)) (b := fun _ : Fin 1 => (0 : Fin 2))
      (fun c : Fin 2 => (c : ZMod 5))).symm)
  have ht := MLE_eval_zeroOne (R := ZMod 5)
    (Fin.append (fun _ : Fin 1 => (1 : Fin 2)) (fun _ : Fin 1 => (0 : Fin 2)))
    (fun v : Fin 2 → Fin 2 => (v 0 : ZMod 5) + 2 * (v 1 : ZMod 5))
  have he := hs.trans (hp.symm.trans ht)
  change eval (fun _ => (0 : ZMod 5)) (splitFirst 1 1 source (fun _ => 1)).val =
    1 + 2 * 0 at he
  simpa only [mul_zero, add_zero] using he

/-- Fixing the last coordinate to one leaves value two at retained zero. -/
theorem suffix_component :
    eval (fun _ => (0 : ZMod 5)) (suffixLayout.components source (fun _ => 1)).val = 2 := by
  change eval (fun _ => (0 : ZMod 5)) (splitLast 1 1 source (fun _ => 1)).val = 2
  have hs := splitLast_eval 1 1 source (fun _ => 1) (fun _ => 0)
  have hp := congrArg (fun r => eval r source.val)
    ((Fin.append_comp (a := fun _ : Fin 1 => (0 : Fin 2)) (b := fun _ : Fin 1 => (1 : Fin 2))
      (fun c : Fin 2 => (c : ZMod 5))).symm)
  have ht := MLE_eval_zeroOne (R := ZMod 5)
    (Fin.append (fun _ : Fin 1 => (0 : Fin 2)) (fun _ : Fin 1 => (1 : Fin 2)))
    (fun v : Fin 2 → Fin 2 => (v 0 : ZMod 5) + 2 * (v 1 : ZMod 5))
  have he := hs.trans (hp.symm.trans ht)
  change eval (fun _ => (0 : ZMod 5)) (splitLast 1 1 source (fun _ => 1)).val =
    0 + 2 * 1 at he
  simpa only [mul_one, zero_add] using he

/-- The two source-coordinate orders produce different component polynomials. -/
theorem prefix_suffix_distinct :
    prefixLayout.components source ≠ suffixLayout.components source := by
  intro h
  have he := congrArg (fun ps => eval (fun _ => (0 : ZMod 5)) (ps (fun _ => 1)).val) h
  rw [prefix_component, suffix_component] at he
  exact (by decide : (1 : ZMod 5) ≠ 2) he

end RingSwitching.Packing.Tests.Layout

end

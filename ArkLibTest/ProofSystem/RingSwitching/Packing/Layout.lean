/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Quirky
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Field.ZMod

/-!
# Packing-layout orientation and quirky-node regressions

A nonconstant source distinguishes prefix and suffix layouts. The quirky fixture has two
skipped nodes, an extra Boolean coordinate and an off-grid query; its component order and
Lagrange node weights exercise the layout without importing a protocol framework.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.Layout

open MvPolynomial Module
open RingSwitching.Packing.ScalarHead

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev ordinaryData : PackingData (ZMod 5) where
  P := (Fin 1 → Fin 2) → ZMod 5
  E := ZMod 5
  ιP := Fin 1 → Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Basis.singleton Unit (ZMod 5)

abbrev prefixLayout := packedPrefixLayout ordinaryData 1 1 (Equiv.refl _)
abbrev suffixLayout := packedSuffixLayout ordinaryData 1 1 (Equiv.refl _)

def source : (ZMod 5)⦃≤ 1⦄[X Fin 2] :=
  ⟨MLE (fun v => (v 0 : ZMod 5) + 2 * (v 1 : ZMod 5)), MLE_mem_restrictDegree _⟩

/-- Fixing the first coordinate to one leaves value one at retained zero. -/
theorem prefix_component :
    eval (fun _ => (0 : ZMod 5)) (prefixLayout.components source (fun _ => 1)).val = 1 := by
  change eval (fun _ => (0 : ZMod 5)) (splitFirst 1 1 source (fun _ => 1)).val = 1
  have hs := splitFirst_eval 1 1 source (fun _ => 1) (fun _ => 0)
  have hp := congrArg (fun r => eval r source.val)
    (cast_append_bool (R := ZMod 5) 1 1 (fun _ => 1) (fun _ => 0))
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
    (cast_append_bool (R := ZMod 5) 1 1 (fun _ => 0) (fun _ => 1))
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

abbrev quirkyData : PackingData (ZMod 5) where
  P := ((Fin 1 → Fin 2) × Fin 2) → ZMod 5
  E := ZMod 5
  ιP := (Fin 1 → Fin 2) × Fin 2
  ιE := Unit
  packBasis := Pi.basisFun _ _
  openBasis := Basis.singleton Unit (ZMod 5)

local instance : Fact (IsField quirkyData.E) := ⟨Field.toIsField (ZMod 5)⟩

/-- The two skipped Boolean indices enumerate field nodes zero and two, not Boolean nodes. -/
def skipNodes : (Fin 1 → Fin 2) ↪ quirkyData.E where
  toFun σ := 2 * (σ 0 : ZMod 5)
  inj' σ τ h := by
    funext i
    fin_cases i
    have he := mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) h
    have hv := congrArg ZMod.val he
    simp only [ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (σ 0).isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans (τ 0).isLt (by decide))] at hv
    exact Fin.ext hv

abbrev quirky := quirkyLayout quirkyData 1 1 skipNodes (Equiv.refl _)

def quirkySource : QuirkyTable (B := ZMod 5) 1 1 :=
  fun yb σ => (yb.1 0 : ZMod 5) + 2 * (σ 0 : ZMod 5) + 3 * (yb.2 : ZMod 5)

def quirkyQuery : quirky.Query := (fun _ => 2, 3, 4)

/-- Off-grid reconstruction uses the certified layout over the same nonconstant source. -/
theorem quirky_off_grid_reconstruction :
    quirky.eval quirkyQuery quirkySource =
      ∑ i, quirky.weight quirkyQuery i *
        aeval (quirky.point quirkyQuery) (quirky.components quirkySource i).val :=
  quirky.reconstruct quirkyQuery quirkySource

/-- The unusual skipped/extra order selects the table value at its retained Boolean point. -/
theorem quirky_component_order :
    eval (fun _ => (0 : ZMod 5))
      (quirky.components quirkySource ((fun _ => 1), 0)).val = 2 ∧
    eval (fun _ => (0 : ZMod 5))
      (quirky.components quirkySource ((fun _ => 0), 1)).val = 3 := by
  constructor <;>
    change eval (fun _ => (0 : ZMod 5)) (MLE _) = _ <;>
    rw [show (fun _ : Fin 1 => (0 : ZMod 5)) =
      ((fun _ : Fin 1 => (0 : Fin 2)) : Fin 1 → ZMod 5) from rfl, MLE_eval_zeroOne] <;>
    norm_num [quirkySource]

/-- The non-Boolean skip node selects its own section with weight one. -/
theorem quirky_weight_node :
    quirkyWeight quirkyData 1 skipNodes 0 (skipNodes (fun _ => 1)) ((fun _ => 1), 0) = 1 := by
  let : Field quirkyData.E := (show IsField quirkyData.E from Fact.out).toField
  unfold quirkyWeight
  rw [Lagrange.eval_basis_self skipNodes.injective.injOn (Finset.mem_univ _)]
  norm_num [eqTilde, eqPolynomial, singleEqPolynomial]

end RingSwitching.Packing.Tests.Layout

end

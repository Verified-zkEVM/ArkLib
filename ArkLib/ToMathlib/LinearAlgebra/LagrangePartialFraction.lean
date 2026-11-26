/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Lagrange

/-!
# Partial fractions of a Lagrange interpolant

Let `s` be a nonempty finite set of nodes `v i` over a field, injective on `s`, and let `I` be the
Lagrange interpolant of the values `r i`. For a point `x` outside the nodes and any constant `c`,

`(c - I(x)) / Z(x) = ∑ i ∈ s, w i * (c - r i) / (x - v i)`,

where `Z = ∏ i ∈ s, (X - v i)` is the nodal polynomial and `w i = ∏ j ≠ i, (v i - v j)⁻¹` is the
nodal weight. This is the partial-fraction decomposition of `(c - I) / Z`; KZG's
function-binding reduction uses it to combine opening proofs into one ARSDH answer.

## Main statements

* `Lagrange.eval_interpolate_const`: interpolating a constant gives that constant.
* `Lagrange.eval_nodal_inv_mul_sub_eval_interpolate`: the partial-fraction identity above.
-/

@[expose] public section

open Polynomial Finset

namespace Lagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F}

/-- Interpolating the constant values `c` on a nonempty set of distinct nodes gives `C c`. -/
theorem interpolate_const (hvs : Set.InjOn v s) (hs : s.Nonempty) (c : F) :
    interpolate s v (fun _ => c) = C c := by
  have hc : (fun _ : ι => c) = c • (1 : ι → F) := by
    funext i
    simp
  rw [hc, map_smul, interpolate_one hvs hs, smul_eq_C_mul, mul_one]

/-- Evaluating the interpolant of a constant gives that constant. -/
theorem eval_interpolate_const (hvs : Set.InjOn v s) (hs : s.Nonempty) (c x : F) :
    eval x (interpolate s v (fun _ => c)) = c := by
  rw [interpolate_const hvs hs, eval_C]

/-- Partial-fraction identity for a Lagrange interpolant: off the nodes,
`(c - I(x)) / Z(x) = ∑ i ∈ s, w i * (x - v i)⁻¹ * (c - r i)`, where `Z` is the nodal polynomial
and `w` the nodal weights. -/
theorem eval_nodal_inv_mul_sub_eval_interpolate (r : ι → F) (hvs : Set.InjOn v s)
    (hs : s.Nonempty) {x : F} (hx : ∀ i ∈ s, x ≠ v i) (c : F) :
    (eval x (nodal s v))⁻¹ * (c - eval x (interpolate s v r)) =
      ∑ i ∈ s, nodalWeight s v i * (x - v i)⁻¹ * (c - r i) := by
  have hsub : interpolate s v (fun i => c - r i) =
      interpolate s v (fun _ => c) - interpolate s v r := by
    rw [← map_sub]
    rfl
  have key := eval_interpolate_not_at_node (fun i => c - r i) hx
  rw [hsub, eval_sub, eval_interpolate_const hvs hs] at key
  rw [key, ← mul_assoc, inv_mul_cancel₀ (eval_nodal_not_at_node hx), one_mul]

end Lagrange

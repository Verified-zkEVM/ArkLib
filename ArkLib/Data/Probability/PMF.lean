/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Probability.Distributions.Uniform

import ToMathlib.Probability.ProbabilityMassFunction.Lemmas

/-!
# Probability mass function event formulas

This module provides an indicator sum formula for the mass of a proposition under a PMF, and
transport results for PMFs mapped along functions and equivalences.

## Main statements

* `PMF.map_true_eq_tsum_indicator` expresses the mass of a proposition as an indicator sum.
* `PMF.map_comp_eq_of_map_eq` transports a pushforward through an equality of PMFs.
* `PMF.uniformOfFintype_event_equiv` transports finite uniform event probabilities.

## References
-/

@[expose] public section

open scoped ENNReal

namespace PMF

/-- The mass assigned to `True` by mapping a PMF along a predicate is an indicator sum. -/
theorem map_true_eq_tsum_indicator {α : Type*} (p : PMF α) (P : α → Prop)
    [DecidablePred P] :
    (p.map P) True = ∑' a, p a * (if P a then (1 : ENNReal) else 0) := by
  rw [PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases h : P a <;> simp [h]

/-- Mapping a pushforward again agrees with mapping the target PMF. -/
theorem map_comp_eq_of_map_eq {α β γ : Type*} (p : PMF α) (q : PMF β)
    (f : α → β) (g : β → γ) (hmap : p.map f = q) :
    p.map (g ∘ f) = q.map g := by
  calc
    p.map (g ∘ f) = (p.map f).map g := (PMF.map_comp (p := p) (f := f) g).symm
    _ = q.map g := congrArg (fun r : PMF β => r.map g) hmap

/-- Uniform event probabilities agree under an equivalence of finite sample spaces. -/
theorem uniformOfFintype_event_equiv {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) (P : β → Prop) :
    ((PMF.uniformOfFintype α).map (P ∘ e)) True =
      ((PMF.uniformOfFintype β).map P) True := by
  exact congrArg (fun p : PMF Prop => p True)
    (map_comp_eq_of_map_eq _ _ e P
      (PMF.uniformOfFintype_map_of_bijective e e.bijective))

end PMF

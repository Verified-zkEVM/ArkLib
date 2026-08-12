/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši
-/

import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform

/-!
  # Notation for probability sampling statements

  The goal is to be able to write readable statements like:
  ```
  Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ F × F }[ z = (x, y) ]
  ```
  which should parse as:
  ```
  (do let x ← PMF.uniformOfFintype F
      let y ← PMF.uniformOfFintype F
      let z ← PMF.uniformOfFintype (F × F)
      return z = (x, y)).val True
  ```
  The `.val True` is used to extract the probability of the condition holding.

  In general the `do` notation is more restrictive than `PMF.bind`, as the latter allows for
  changing universe levels. This should not be an issue in general if we always work over `Type`.

  We should also allow for non-uniform distributions, e.g.
  `Pr_{ let e ← discreteGaussian (ZMod p) }[ e = 0 ]`.
-/

open scoped ProbabilityTheory NNReal ENNReal

open Lean Elab Parser Term Meta PMF

namespace ProbabilityTheory

/-- Notation for uniform sampling from a finite, non-empty type. Just converts to
  `PMF.uniformOfFintype`. -/
scoped notation "$ᵖ" => PMF.uniformOfFintype

/--
Syntax for probability expressions: `Pr_{...}[...]`

Expands `Pr_{e₁; e₂; ...; eₙ}[cond]` to `(do e₁; e₂; ...; eₙ; return cond).val True`.

The do-notation uses the `Bind` typeclass, which requires all sampled types to live in the same
universe. In practice this is not a restriction since all our probability distributions sample from
`Type` (finite fields, finite sets, etc.) and conditions are in `Prop`.

If you somehow need universe polymorphism (sampling from `Type u` and returning something in
`Type v`), you'd need to manually use `PMF.bind` instead of this notation. But this never happens
in cryptographic applications.

# Examples
```
Pr_{ let x ←$ᵖ F; let y ←$ᵖ F }[x = y]
```
expands to
```
(do let x ← PMF.uniformOfFintype F; let y ← PMF.uniformOfFintype F; return x = y).val True
```
-/
syntax (name := prStx) "Pr_{" doSeq "}[" term "]" : term

/--
Elaboration rule for `Pr_{...}[...]` notation.

Handles both `doSeqBracketed` (curly braces) and `doSeqIndent` (no braces) forms of do-sequences.
-/
scoped macro_rules (kind := prStx)
  -- `doSeqBracketed`
  | `(Pr_{{$items*}}[$t]) => `((((do $items:doSeqItem*
                                     return $t:term) True) : ENNReal))
  -- `doSeqIndent`
  | `(Pr_{$items*}[$t]) => `((((do $items:doSeqItem*
                                     return $t:term) True) : ENNReal))

/-- Unfold a single-sample event as an indicator-weighted `tsum` over the `PMF`. -/
lemma Pr_eq_tsum_indicator {α : Type} (p : PMF α) (P : α → Prop)
    [DecidablePred P] :
    Pr_{ let a ← p }[P a] =
      ∑' a, p a * (if P a then (1 : ENNReal) else 0) := by
  simp only [Bind.bind, Pure.pure, PMF.bind, PMF.pure, DFunLike.coe,
    eq_iff_iff, true_iff]

/-- Uniform probability is invariant under an equivalence of finite sample spaces. -/
lemma Pr_uniform_equiv {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) (P : β → Prop) :
    Pr_{let a ← $ᵖ α}[P (e a)] = Pr_{let b ← $ᵖ β}[P b] := by
  classical
  have hmap : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
    ext b
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply,
      Fintype.card_congr e, tsum_fintype]
    have hs :
        Finset.univ.sum (fun a : α =>
            if b = e a then (Fintype.card β : ENNReal)⁻¹ else 0) =
          Finset.univ.sum (fun b' : β =>
            if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0) := by
      simpa using
        (Fintype.sum_equiv e
          (fun a : α => if b = e a then (Fintype.card β : ENNReal)⁻¹ else 0)
          (fun b' : β => if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0)
          (by intro a; rfl))
    exact hs.trans (by simp)
  change
    (PMF.uniformOfFintype α).map (P ∘ e) True =
      (PMF.uniformOfFintype β).map P True
  have hcomp :
      (PMF.uniformOfFintype α).map (P ∘ e) =
        ((PMF.uniformOfFintype α).map e).map P := by
    simpa [Function.comp] using
      (PMF.map_comp (p := PMF.uniformOfFintype α) (f := e) (g := P)).symm
  exact congrArg (fun q : PMF Prop => q True) (hcomp.trans (by rw [hmap]))

end ProbabilityTheory

example {F} [Fintype F] [Nonempty F] :
  Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ (F × F) }[z = (x, y)] =
  (do let x ← PMF.uniformOfFintype F
      let y ← PMF.uniformOfFintype F
      let z ← PMF.uniformOfFintype (F × F)
      return (z = (x, y))).val True := rfl

section

variable {F : Type} [Nonempty F] [Fintype F]

example :
  (do
    let x ← $ᵖ F
    let y ← $ᵖ F
    let z ← $ᵖ (F × F)
    return z = (x, y) : PMF Prop).1 True = ((1 : ℝ≥0∞) / Fintype.card (F × F)) := by
  classical
  simp [Bind.bind, Pure.pure, PMF.bind]
  simp [DFunLike.coe]
  ring_nf
  rw [mul_comm (_ ^ 2) _, mul_assoc, ENNReal.mul_inv_cancel, mul_one, ENNReal.inv_pow]
  <;> aesop

example :
  Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ (F × F) }[ z = (x, y) ] =
  ((1 : ℝ≥0∞) / Fintype.card (F × F)) ↔
  (do
    let x ← $ᵖ F
    let y ← $ᵖ F
    let z ← $ᵖ (F × F)
    return z = (x, y)).val True = ((1 : ℝ≥0∞) / Fintype.card (F × F)) := by
  rfl

end

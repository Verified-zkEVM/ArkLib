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

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Probability.Instances

/-!
# The claim-reduction step

Many rounds reduce a claim about a polynomial to a claim about its value at a random point: the
prover sends a univariate polynomial `g` of bounded degree, the verifier checks it and draws a
challenge `r`, and the next claim is about `g(r)`. If the input claim is false, the honest
polynomial `h` that a true claim would require differs from `g`, and the output claim can be
true only if `g` and `h` agree at `r`. This module bounds the probability of that event.

* `agreement_le`: a degree-`≤ d` polynomial that differs from another one at some point agrees
  with it at a uniform challenge with probability at most `d / |R|`.
* `agreement_le_field`: the same over a field, for distinct polynomials.
* `claimReduction_le`: the claim-reduction step for one check and one output claim.
* `reduction_le`: the form that the kit's per-round obligation `RoundSound` uses, for an event
  whose every outcome forces a difference somewhere and an agreement at the challenge.

## Design choices

* **The step is stated without the kit.** Its hypotheses mention only the claims, the check and
  the two polynomials, so a round of any protocol can use it, and the kit's instances
  (`Specs.Kit.Sumcheck`) apply it pointwise.
* **Difference is pointwise.** Over a finite semiring two distinct polynomials of degree at most
  `d` can agree at every point, so `agreement_le` and `claimReduction_le` take a point of
  difference. Over a field `agreement_le_field` takes `g ≠ h`.
-/

namespace Specs.Kit

open scoped ENNReal NNReal
open Polynomial OracleComp

section ClaimReduction

variable {R : Type} [CommSemiring R] [IsDomain R] [Fintype R] [SampleableType R] {d : ℕ}

/-- **Polynomial agreement.** A degree-`≤ d` message `g` that differs from a claimed honest
polynomial `h` at some point agrees with it at a uniform challenge with probability at most
`d / |R|`. -/
theorem agreement_le (g h : R⦃≤ d⦄[X]) (hne : ∃ a, g.val.eval a ≠ h.val.eval a) :
    Pr{let r ← $ᵗ R}[g.val.eval r = h.val.eval r] ≤
      (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨a, ha⟩ := hne
  exact Probability.prob_agreement_of_sum_ne {a} g h (by simpa using ha)

/-- **Polynomial agreement over a field.** Distinct degree-`≤ d` polynomials agree at a uniform
challenge with probability at most `d / |F|`. -/
theorem agreement_le_field {F : Type} [Field F] [Fintype F] [SampleableType F]
    (g h : F⦃≤ d⦄[X]) (hne : g ≠ h) :
    Pr{let r ← $ᵗ F}[g.val.eval r = h.val.eval r] ≤
      (((d : ℝ≥0) / Fintype.card F : ℝ≥0) : ℝ≥0∞) :=
  Probability.prob_degreeLE_eval_eq_le hne

/-- **The claim-reduction step.** Suppose a round reduces the input claim `claimIn` to the output
claim `claimOut r` at the challenge `r`, with message `g` and honest polynomial `h`, such that

* `hhonest`: if the check passes and the input claim is false, then `g` differs from `h` at some
  point;
* `hout`: if the check passes, a true output claim at `r` means that `g` and `h` agree at `r`.

Then from a false input claim, the check passes and the output claim is true with probability
at most `d / |R|`. -/
theorem claimReduction_le (claimIn check : Prop) (claimOut : R → Prop) (g h : R⦃≤ d⦄[X])
    (hhonest : check → ¬ claimIn → ∃ a, g.val.eval a ≠ h.val.eval a)
    (hout : ∀ r, check → claimOut r → g.val.eval r = h.val.eval r) (hfalse : ¬ claimIn) :
    Pr{let r ← $ᵗ R}[check ∧ claimOut r] ≤ (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  by_cases hc : check
  · exact (prEvent_mono _ _ _ fun r hr => hout r hc hr.2).trans
      (agreement_le g h (hhonest hc hfalse))
  · rw [prEvent_eq_zero_of_forall_not _ _ fun _ hr => hc hr.1]
    exact zero_le

/-- **The claim-reduction step for an event.** If every outcome `r` of the event makes the
message `g` differ from the honest polynomial `h` somewhere and agree with it at `r`, the event
has probability at most `d / |R|`. -/
theorem reduction_le (event : R → Prop) (g h : R⦃≤ d⦄[X])
    (hreduce : ∀ r, event r → (∃ a, g.val.eval a ≠ h.val.eval a) ∧
      g.val.eval r = h.val.eval r) :
    Pr{let r ← $ᵗ R}[event r] ≤ (((d : ℝ≥0) / Fintype.card R : ℝ≥0) : ℝ≥0∞) := by
  by_cases hne : ∃ a, g.val.eval a ≠ h.val.eval a
  · exact (prEvent_mono _ _ _ fun r hr => (hreduce r hr).2).trans (agreement_le g h hne)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun r hr => hne (hreduce r hr).1]
    exact zero_le

end ClaimReduction

end Specs.Kit

/-! ## Axioms -/

#print axioms Specs.Kit.agreement_le
#print axioms Specs.Kit.agreement_le_field
#print axioms Specs.Kit.claimReduction_le
#print axioms Specs.Kit.reduction_le

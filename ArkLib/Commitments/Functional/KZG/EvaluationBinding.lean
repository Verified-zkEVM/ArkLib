/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.Basic

/-!
# KZG evaluation binding: the t-SDH reduction

An evaluation-binding adversary outputs a commitment `cm`, a point `q`, and two accepted
openings `(r₁, π₁)` and `(r₂, π₂)` at `q` with `r₁ ≠ r₂`. Subtracting the two opening equations
`cm - rᵢ • g₁ = (τ - q) • πᵢ` gives `(r₂ - r₁) • g₁ = (τ - q) • (π₁ - π₂)`, so
`(r₂ - r₁)⁻¹ • (π₁ - π₂) = (τ - q)⁻¹ • g₁`. The pair `(-q, (r₂ - r₁)⁻¹ • (π₁ - π₂))` therefore
wins `TSDH.experiment`, whose win predicate is `τ + c ≠ 0 ∧ h = (τ + c)⁻¹ • g₁`. The case
`τ = q` cannot occur: it would force `r₁ = r₂`.

The reduction uses one subtraction and one scalar multiplication in `G₁`. This file states the
pointwise algebra only; the game-level statement is built on top of it separately.

## Main statements

* `KZG.evalBindingReduction`: the t-SDH answer computed from two conflicting openings.
* `KZG.inv_sub_smul_of_opening_eqs`: the algebra behind the reduction.
* `KZG.evalBindingReduction_wins`: two accepted conflicting openings give a t-SDH win.

## References

* [Kate, A., Zaverucha, G. M., and Goldberg, I., *Polynomial Commitments*][KZG10TR]
-/

@[expose] public section

namespace KZG

variable {F : Type} [Field F]
variable {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ]

/-- The t-SDH answer `(-q, (r₂ - r₁)⁻¹ • (π₁ - π₂))` computed from two openings `(r₁, π₁)` and
`(r₂, π₂)` of one commitment at the same point `q`. -/
def evalBindingReduction (q r₁ : F) (π₁ : G₁) (r₂ : F) (π₂ : G₁) : F × G₁ :=
  (-q, (r₂ - r₁)⁻¹ • (π₁ - π₂))

/-- Two opening equations at the same point `q` with different values determine
`(τ - q)⁻¹ • g₁`, and force `τ ≠ q`. -/
theorem inv_sub_smul_of_opening_eqs {g₁ : G₁} (hg₁ : g₁ ≠ 0) {τ q r₁ r₂ : F} {cm π₁ π₂ : G₁}
    (h₁ : cm - r₁ • g₁ = (τ - q) • π₁) (h₂ : cm - r₂ • g₁ = (τ - q) • π₂) (hr : r₁ ≠ r₂) :
    τ - q ≠ 0 ∧ (r₂ - r₁)⁻¹ • (π₁ - π₂) = (τ - q)⁻¹ • g₁ := by
  have hsub : (τ - q) • (π₁ - π₂) = (r₂ - r₁) • g₁ := by
    rw [smul_sub, ← h₁, ← h₂, sub_smul]
    abel
  have hr' : r₂ - r₁ ≠ 0 := sub_ne_zero.mpr hr.symm
  have hτq : τ - q ≠ 0 := by
    intro h
    rw [h, zero_smul, eq_comm, smul_eq_zero] at hsub
    exact hsub.elim hr' hg₁
  refine ⟨hτq, ?_⟩
  have hπ : π₁ - π₂ = ((τ - q)⁻¹ * (r₂ - r₁)) • g₁ := by
    rw [mul_smul, ← hsub, smul_smul, inv_mul_cancel₀ hτq, one_smul]
  rw [hπ, smul_smul, ← mul_assoc, mul_comm (r₂ - r₁)⁻¹, mul_assoc, inv_mul_cancel₀ hr', mul_one]

/-- **Evaluation binding reduces to t-SDH, pointwise.** If `e g₁ g₂ ≠ 0`, `g₁` generates `G₁`,
and two openings of `cm` at `q` with values `r₁ ≠ r₂` are both accepted under the honest
verifier key for `τ`, then `evalBindingReduction` satisfies the win predicate of
`TSDH.experiment`. -/
theorem evalBindingReduction_wins [DecidableEq Gₜ] {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁}
    {g₂ : G₂} (he : e g₁ g₂ ≠ 0) (hg₁ : Function.Surjective (· • g₁ : F → G₁)) (τ : F)
    {cm : G₁} {q r₁ r₂ : F} {π₁ π₂ : G₁}
    (h₁ : verifyOpening e g₁ (verifierKey g₂ τ) cm q r₁ π₁ = true)
    (h₂ : verifyOpening e g₁ (verifierKey g₂ τ) cm q r₂ π₂ = true) (hr : r₁ ≠ r₂) :
    τ + (evalBindingReduction q r₁ π₁ r₂ π₂).1 ≠ 0 ∧
      (evalBindingReduction q r₁ π₁ r₂ π₂).2 =
        (τ + (evalBindingReduction q r₁ π₁ r₂ π₂).1)⁻¹ • g₁ := by
  simpa only [evalBindingReduction, ← sub_eq_add_neg] using
    inv_sub_smul_of_opening_eqs (ne_zero_left_of_pairing_ne_zero he)
      (verifyOpening_eq he hg₁ h₁) (verifyOpening_eq he hg₁ h₂) hr

end KZG

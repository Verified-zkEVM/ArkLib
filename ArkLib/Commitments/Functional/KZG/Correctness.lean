/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.Basic

/-!
# Correctness of KZG openings

For every trapdoor `τ`, coefficient vector `c` and point `q`, the honest verifier accepts the
honest commitment, the true value `evaluate c q`, and the honest opening proof. The statement is
pointwise in `τ`; it needs no hypothesis on the pairing or the generators.

## Main statements

* `KZG.toPoly_quotient`: the computable quotient is Mathlib's `(f - C (f q)) /ₘ (X - C q)`.
* `KZG.verifyOpening_generateOpening`: honest openings are accepted.
-/

@[expose] public section

open CompPoly

namespace KZG

variable {F : Type} [Field F] [DecidableEq F]
variable {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ]
variable {n : ℕ}

/-- The computable opening quotient agrees with Mathlib's division by the monic `X - C q`. -/
theorem toPoly_quotient (c : Fin (n + 1) → F) (q : F) :
    (quotient c q).toPoly =
      ((CPolynomial.ofFn c).toPoly - Polynomial.C (evaluate c q)) /ₘ
        (Polynomial.X - Polynomial.C q) := by
  have hmonic : (CPolynomial.X - CPolynomial.C q : CPolynomial F).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_sub, CPolynomial.X_toPoly,
      CPolynomial.C_toPoly]
    exact Polynomial.monic_X_sub_C q
  rw [quotient, CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ hmonic, CPolynomial.toPoly_sub,
    CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly, CPolynomial.C_toPoly]

/-- The opening quotient has degree at most `n`. -/
theorem natDegree_toPoly_quotient_le (c : Fin (n + 1) → F) (q : F) :
    (quotient c q).toPoly.natDegree ≤ n := by
  rw [toPoly_quotient, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C q)]
  refine (Nat.sub_le _ _).trans ?_
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le (natDegree_toPoly_ofFn_le c) ?_)
  rw [Polynomial.natDegree_C]
  exact Nat.zero_le n

/-- The opening quotient `Q` satisfies `(x - q) * Q(x) = f(x) - f(q)` at every point `x`. -/
theorem sub_mul_eval_quotient (c : Fin (n + 1) → F) (q x : F) :
    (x - q) * (quotient c q).toPoly.eval x = evaluate c x - evaluate c q := by
  have hroot : ((CPolynomial.ofFn c).toPoly - Polynomial.C (evaluate c q)).IsRoot q := by
    simp [evaluate_eq_eval_toPoly]
  have hmul := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  rw [toPoly_quotient, evaluate_eq_eval_toPoly c x]
  have := congrArg (Polynomial.eval x) hmul
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    using this

/-- An honest opening proof is `Q(τ) • g₁` for the opening quotient `Q`. -/
theorem generateOpening_committerKey (g₁ : G₁) (τ : F) (c : Fin (n + 1) → F) (q : F) :
    generateOpening (committerKey g₁ τ n) c q = (quotient c q).toPoly.eval τ • g₁ :=
  commit_committerKey_of_coeff g₁ τ (natDegree_toPoly_quotient_le c q) _
    fun _ => CPolynomial.coeff_toPoly _ _

/-- **Correctness.** For every trapdoor `τ`, the honest verifier accepts the honest commitment
to `c`, the value `evaluate c q` and the honest opening proof at `q`. -/
theorem verifyOpening_generateOpening [DecidableEq Gₜ] (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁)
    (g₂ : G₂) (τ : F) (c : Fin (n + 1) → F) (q : F) :
    verifyOpening e g₁ (verifierKey g₂ τ) (commit (committerKey g₁ τ n) c) q (evaluate c q)
      (generateOpening (committerKey g₁ τ n) c q) = true := by
  refine decide_eq_true ?_
  simp only [verifierKey, Matrix.cons_val_zero, Matrix.cons_val_one, commit_committerKey,
    generateOpening_committerKey, ← sub_smul, map_smul, LinearMap.smul_apply, smul_smul]
  rw [← sub_mul_eval_quotient c q τ, mul_comm]

end KZG

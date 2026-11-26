/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Quang Dao
-/
module

public import CompPoly.Univariate.Basic
public import CompPoly.Univariate.ToPoly
public import CompPoly.Univariate.DivisionCorrectness
public import Mathlib.Algebra.Polynomial.FieldDivision
public import VCVio.CryptoFoundations.GroupModel.Typed
public import VCVio.CryptoFoundations.HardnessAssumptions.SDH

/-!
# The KZG polynomial commitment scheme

This file defines the algorithms of the KZG polynomial commitment scheme [KZG10] in VCVio's
additive conventions, together with the pointwise algebra that the security reductions use.

## Setting

The scalars form a field `F`. The source groups `G₁`, `G₂` and the target group `Gₜ` are
`F`-modules, written additively, with a bilinear pairing `e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ` and generators
`g₁ : G₁` and `g₂ : G₂`. The security lemmas assume `e g₁ g₂ ≠ 0` and that every element of `G₁`
is a multiple of `g₁`; both hypotheses are passed unbundled.

The only realizable instance is `F = ZMod r` for the prime order `r` of the groups: a cyclic group
of prime order `r` is a `ZMod r`-module, and no other field acts on it. The generic field is a
harmless generalization that keeps the statements free of `ZMod` casts.

## Algorithms

* `keygen` samples a nonzero trapdoor `τ` with `SDH.sampleTrapdoor` and returns the committer key
  `committerKey g₁ τ n = (τ ^ i • g₁)ᵢ` and the verifier key `verifierKey g₂ τ = ![g₂, τ • g₂]`.
  These are exactly the reference strings of `TSDH.experiment` and `ARSDH.experiment`.
* Data is a coefficient vector `c : Fin (n + 1) → F`, the polynomial `∑ i, c i * X ^ i` of degree
  at most `n`. `evaluate c x` evaluates it.
* `commit ck c = ∑ i, c i • ck i`.
* `generateOpening ck c q` commits to the quotient `(f - f(q)) / (X - q)`, computed with
  CompPoly's `CPolynomial`.
* `verifyOpening e g₁ vk cm q r π` checks `e (cm - r • g₁) (vk 0) = e π (vk 1 - q • vk 0)`.

All algorithms except `keygen` are computable. `keygen` is noncomputable only because VCVio's
`SDH.sampleTrapdoor` samples from a subtype through a noncomputable `SampleableType` instance.

## Main statements

* `commit_committerKey`: an honest commitment is `evaluate c τ • g₁`.
* `commit_eq_ofCoeffs_point`: a commitment is the point of VCVio's algebraic representation
  `GroupModel.AlgebraicPoint.ofCoeffs ck c`.
* `smul_left_injective_of_pairing_ne_zero`: under `e g₁ g₂ ≠ 0`, `(· • g₁)` is injective.
* `verifyOpening_eq`: an accepted opening `(cm, q, r, π)` satisfies `cm - r • g₁ = (τ - q) • π`.

## References

* [Kate, A., Zaverucha, G. M., and Goldberg, I.,
  *Constant-Size Commitments to Polynomials and Their Applications*][KZG10]
-/

@[expose] public section

open CompPoly

namespace KZG

variable {F : Type} [Field F]
variable {G₁ G₂ Gₜ : Type} [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ]
variable {n : ℕ}

section Algorithms

/-- The committer key `(τ ^ i • g₁)_{i ≤ n}`: the first-source part of the reference string of
`TSDH.experiment` and `ARSDH.experiment`. -/
def committerKey (g₁ : G₁) (τ : F) (n : ℕ) : Fin (n + 1) → G₁ :=
  fun i => τ ^ (i : ℕ) • g₁

/-- The verifier key `![g₂, τ • g₂]`: the second-source part of the reference string of
`TSDH.experiment` and `ARSDH.experiment`. -/
def verifierKey (g₂ : G₂) (τ : F) : Fin 2 → G₂ :=
  ![g₂, τ • g₂]

/-- Key generation samples a uniform nonzero trapdoor and returns both keys. It is noncomputable
only because `SDH.sampleTrapdoor` is. -/
noncomputable def keygen [Fintype F] [DecidableEq F] (g₁ : G₁) (g₂ : G₂) (n : ℕ) :
    ProbComp ((Fin (n + 1) → G₁) × (Fin 2 → G₂)) := do
  let τ ← SDH.sampleTrapdoor F
  return (committerKey g₁ τ n, verifierKey g₂ τ)

/-- Evaluate the polynomial with coefficient vector `c` at `x`. -/
def evaluate [DecidableEq F] (c : Fin (n + 1) → F) (x : F) : F :=
  (CPolynomial.ofFn c).eval x

/-- Commit to the coefficient vector `c`: `∑ i, c i • ck i`. -/
def commit (ck : Fin (n + 1) → G₁) (c : Fin (n + 1) → F) : G₁ :=
  ∑ i, c i • ck i

/-- The opening quotient `(f - f(q)) / (X - q)` of the polynomial `f` with coefficients `c`. -/
def quotient [DecidableEq F] (c : Fin (n + 1) → F) (q : F) : CPolynomial F :=
  (CPolynomial.ofFn c - CPolynomial.C (evaluate c q)).divByMonic
    (CPolynomial.X - CPolynomial.C q)

/-- The opening proof at `q`: the commitment to the quotient `(f - f(q)) / (X - q)`. -/
def generateOpening [DecidableEq F] (ck : Fin (n + 1) → G₁) (c : Fin (n + 1) → F) (q : F) : G₁ :=
  commit ck (fun i => (quotient c q).coeff i)

/-- Accept the claim that the committed polynomial takes value `r` at `q` with proof `π` when
`e (cm - r • g₁) (vk 0) = e π (vk 1 - q • vk 0)`. -/
def verifyOpening [DecidableEq Gₜ] (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (vk : Fin 2 → G₂)
    (cm : G₁) (q r : F) (π : G₁) : Bool :=
  decide (e (cm - r • g₁) (vk 0) = e π (vk 1 - q • vk 0))

end Algorithms

section Commitments

section Coefficients

variable [DecidableEq F]

/-- The coefficients of `CPolynomial.ofFn c`, read through Mathlib's `Polynomial`. -/
theorem coeff_toPoly_ofFn (c : Fin (n + 1) → F) (k : ℕ) :
    (CPolynomial.ofFn c).toPoly.coeff k = if h : k < n + 1 then c ⟨k, h⟩ else 0 := by
  rw [← CPolynomial.coeff_toPoly, CPolynomial.coeff_ofFn]

/-- A coefficient vector of length `n + 1` gives a polynomial of degree at most `n`. -/
theorem natDegree_toPoly_ofFn_le (c : Fin (n + 1) → F) :
    (CPolynomial.ofFn c).toPoly.natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_toPoly_ofFn]
  split_ifs <;> first | rfl | omega

/-- Evaluation of a coefficient vector is Mathlib evaluation of the corresponding polynomial. -/
theorem evaluate_eq_eval_toPoly (c : Fin (n + 1) → F) (x : F) :
    evaluate c x = (CPolynomial.ofFn c).toPoly.eval x :=
  CPolynomial.eval_toPoly x _

/-- If `p` has degree at most `n`, the coefficient vector of its first `n + 1` coefficients
represents `p`. -/
theorem toPoly_ofFn_coeff {p : Polynomial F} (hp : p.natDegree ≤ n) :
    (CPolynomial.ofFn (fun i : Fin (n + 1) => p.coeff i)).toPoly = p := by
  ext k
  rw [coeff_toPoly_ofFn]
  split_ifs with hk
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

end Coefficients

/-- An honest commitment to coefficients `c` of a polynomial `p` of degree at most `n` is
`p.eval τ • g₁`. -/
theorem commit_committerKey_of_coeff (g₁ : G₁) (τ : F) {p : Polynomial F} (hp : p.natDegree ≤ n)
    (c : Fin (n + 1) → F) (hc : ∀ i, c i = p.coeff i) :
    commit (committerKey g₁ τ n) c = p.eval τ • g₁ := by
  simp only [commit, committerKey, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Polynomial.eval_eq_sum_range' (n := n + 1) (by omega),
    ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * τ ^ i)]
  simp [hc]

/-- An honest commitment to coefficients `c` is `evaluate c τ • g₁`. -/
theorem commit_committerKey [DecidableEq F] (g₁ : G₁) (τ : F) (c : Fin (n + 1) → F) :
    commit (committerKey g₁ τ n) c = evaluate c τ • g₁ := by
  rw [evaluate_eq_eval_toPoly]
  refine commit_committerKey_of_coeff g₁ τ (natDegree_toPoly_ofFn_le c) c fun i => ?_
  simp only [coeff_toPoly_ofFn, Fin.is_lt, dite_true]

/-- A commitment is the point of VCVio's algebraic representation with coefficients `c` over the
basis `ck`. -/
theorem commit_eq_ofCoeffs_point (ck : Fin (n + 1) → G₁) (c : Fin (n + 1) → F) :
    commit ck c = (GroupModel.AlgebraicPoint.ofCoeffs ck c).point :=
  rfl

end Commitments

section Pairing

variable {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}

/-- A nondegenerate pairing value forces a nonzero first generator. -/
theorem ne_zero_left_of_pairing_ne_zero (he : e g₁ g₂ ≠ 0) : g₁ ≠ 0 := by
  rintro rfl
  simp at he

/-- A nondegenerate pairing value forces a nonzero second generator. -/
theorem ne_zero_right_of_pairing_ne_zero (he : e g₁ g₂ ≠ 0) : g₂ ≠ 0 := by
  rintro rfl
  simp at he

/-- Under `e g₁ g₂ ≠ 0`, scalars are determined by their multiples of `g₁`. -/
theorem smul_left_injective_of_pairing_ne_zero (he : e g₁ g₂ ≠ 0) :
    Function.Injective (· • g₁ : F → G₁) :=
  smul_left_injective F (ne_zero_left_of_pairing_ne_zero he)

/-- Under `e g₁ g₂ ≠ 0`, scalars are determined by their multiples of `g₂`. -/
theorem smul_right_injective_of_pairing_ne_zero (he : e g₁ g₂ ≠ 0) :
    Function.Injective (· • g₂ : F → G₂) :=
  smul_left_injective F (ne_zero_right_of_pairing_ne_zero he)

/-- When `g₁` generates `G₁` and `e g₁ g₂ ≠ 0`, pairing with `g₂` is injective on `G₁`. -/
theorem eq_of_pairing_eq (he : e g₁ g₂ ≠ 0) (hg₁ : Function.Surjective (· • g₁ : F → G₁))
    {x y : G₁} (h : e x g₂ = e y g₂) : x = y := by
  obtain ⟨a, ha⟩ := hg₁ (x - y)
  have hzero : e (x - y) g₂ = 0 := by
    rw [map_sub, LinearMap.sub_apply, h, sub_self]
  rw [← ha] at hzero
  simp only [map_smul, LinearMap.smul_apply, smul_eq_zero, he, or_false] at hzero
  rw [← sub_eq_zero, ← ha, hzero]
  exact zero_smul F g₁

/-- **Opening equation.** If `e g₁ g₂ ≠ 0` and `g₁` generates `G₁`, an opening `(cm, q, r, π)`
accepted under the honest verifier key satisfies `cm - r • g₁ = (τ - q) • π`. -/
theorem verifyOpening_eq [DecidableEq Gₜ] (he : e g₁ g₂ ≠ 0)
    (hg₁ : Function.Surjective (· • g₁ : F → G₁)) {τ : F} {cm : G₁} {q r : F} {π : G₁}
    (h : verifyOpening e g₁ (verifierKey g₂ τ) cm q r π = true) :
    cm - r • g₁ = (τ - q) • π := by
  have h' := of_decide_eq_true h
  simp only [verifierKey, Matrix.cons_val_zero, Matrix.cons_val_one] at h'
  refine eq_of_pairing_eq he hg₁ ?_
  rw [h', ← sub_smul, map_smul, map_smul, LinearMap.smul_apply]

end Pairing

end KZG

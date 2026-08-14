/-
Copyright (c) 2025-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Tobias Rothmann
-/
import ArkLib.Data.MvPolynomial.Degrees

/-!
# Degree-bounded coefficient transport through a ring embedding

The multivariate leg of the claim-transport layer (see the folder umbrella
`ArkLib/ProofSystem/RingSwitching/Transport.lean`): reinterpret a multivariate polynomial
with coefficients in a base ring `R` as one over a target carrier `T`, without changing its
shape.

* `embedCoeffs φ : R⦃≤ d⦄[X σ] → T⦃≤ d⦄[X σ]` — component-wise coefficient transport along a
  ring hom `φ : R →+* T`. The individual degree bound `d` is preserved for free
  (`MvPolynomial.map` never enlarges supports), so degree-bounded polynomial families —
  multilinears at `d = 1`, higher-degree sumcheck round polynomials at larger `d` — stay in
  their class under transport.
* `embedCoeffs_eval` — transport commutes with evaluation: evaluating the transported
  polynomial at transported points computes the transported evaluation. This is the
  multivariate analogue of `evalAt_apply` and the identity that lets a verifier interpret a
  base-ring polynomial inside the carrier where its checks run.

The univariate leg — evaluation through an embedding and the interpolation kernel — is the
sibling file `Eval.lean`. In this folder, `Packing`
(`RingSwitching/Packing/`) consumes the multilinear case `d = 1` to embed the packed
polynomial into its pack/trace carrier.
-/

open MvPolynomial

namespace RingSwitching

section CoeffTransport

variable {R T : Type*} [CommSemiring R] [CommSemiring T] {σ : Type*} {d : ℕ}

open scoped MvPolynomial in
/-- Component-wise coefficient transport of a degree-bounded multivariate polynomial along a
ring hom: apply `φ` to every coefficient via `MvPolynomial.map`. Individual degree bounds are
preserved because mapping never enlarges the support. -/
noncomputable def embedCoeffs (φ : R →+* T) (p : R⦃≤ d⦄[X σ]) : T⦃≤ d⦄[X σ] :=
  ⟨MvPolynomial.map (f := φ) p.val, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    calc
      MvPolynomial.degreeOf i (MvPolynomial.map φ p.val)
      _ ≤ MvPolynomial.degreeOf i p.val := by
        refine degreeOf_le_iff.mpr ?_
        intro m hm
        have hm' : m ∈ p.val.support := by
          apply MvPolynomial.support_map_subset (f := φ)
          exact hm
        exact monomial_le_degreeOf i hm'
      _ ≤ d := by
        have hp := p.property
        rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le] at hp
        exact hp i⟩

open scoped MvPolynomial in
/-- Evaluating the coefficient-transported polynomial at transported points computes the
transported evaluation — the multivariate analogue of `evalAt_apply`. -/
theorem embedCoeffs_eval (φ : R →+* T) (p : R⦃≤ d⦄[X σ]) (x : σ → R) :
    (embedCoeffs φ p).val.eval (fun i => φ (x i)) = φ (p.val.eval x) := by
  rw [show (embedCoeffs φ p).val = MvPolynomial.map φ p.val from rfl,
    MvPolynomial.eval_map]
  have h := MvPolynomial.eval₂_comp_left φ (RingHom.id R) x p.val
  simp only [RingHom.comp_id, Function.comp_def] at h
  rw [← h]
  rfl

end CoeffTransport

end RingSwitching

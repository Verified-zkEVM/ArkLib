/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.Data.Probability.Instances
public import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Affine batching of a polynomial family

A nonzero constant term or one nonzero polynomial fixed before the evaluation challenge suffices
for a batching bound. Only the selected polynomial's degree is charged; the family size does not
multiply the error. The multilinear-table specialization charges the number of row variables.

These are proof-layer bounds in the existing `ProbComp` semantics. Their polynomial arguments are
mathematical views; they do not construct a runtime polynomial representation or a new sampler.
-/

@[expose] public section

open scoped BigOperators ProbabilityTheory ENNReal

namespace Probability

/-- Affine batching hides a fixed nonzero constant or a selected nonzero polynomial only through
that polynomial's root event or one nontrivial affine equation. The selected index is fixed before
either fresh challenge is sampled. -/
theorem prob_affine_batch_eq_zero_le {F : Type} [Field F] [Fintype F] [SampleableType F]
    {n K d : ℕ} (S : F) (p : Fin K → MvPolynomial (Fin n) F)
    (hnontrivial : S ≠ 0 ∨ ∃ k, p k ≠ 0 ∧ (p k).totalDegree ≤ d) :
    Pr{let r ← $ᵗ ((Fin n → F) × (Fin K → F))}[
      S + ∑ k, MvPolynomial.eval r.1 (p k) * r.2 k = 0] ≤
      (d : ENNReal) / Fintype.card F + (Fintype.card F : ENNReal)⁻¹ := by
  classical
  let event : (Fin n → F) × (Fin K → F) → Prop :=
    fun r ↦ S + ∑ k, MvPolynomial.eval r.1 (p k) * r.2 k = 0
  by_cases hS : S ≠ 0
  · have hbatch : Pr{let r ← $ᵗ ((Fin n → F) × (Fin K → F))}[event r] ≤
        (Fintype.card F : ENNReal)⁻¹ :=
      SampleableType.prEvent_uniformSample_prod_le_of_forall_fst event fun z ↦
        prob_affine_dotProduct_eq_zero_le S (fun k ↦ MvPolynomial.eval z (p k)) (Or.inl hS)
    exact hbatch.trans le_add_self
  · obtain ⟨k, hpk, hdeg⟩ := hnontrivial.resolve_left hS
    have hhide := Probability.prob_schwartz_zippel_mv_polynomial_of_totalDegree_le
      (p k) hpk hdeg
    rw [SampleableType.prEvent_uniformSample_prod]
    have hbind := prEvent_bind_le_prEvent_add ($ᵗ (Fin n → F))
      (fun z ↦ do let l ← $ᵗ (Fin K → F); pure (z, l))
      (fun z ↦ MvPolynomial.eval z (p k) = 0) event (ε := (Fintype.card F : ENNReal)⁻¹)
      (by
        intro z hz
        have hd : (fun j ↦ MvPolynomial.eval z (p j)) ≠ 0 := by
          intro hd
          exact hz (by simpa using congrFun hd k)
        simpa only [prEvent_norm, event] using
          prob_affine_dotProduct_eq_zero_le S (fun j ↦ MvPolynomial.eval z (p j)) (Or.inr hd))
    simpa only [prEvent_norm] using hbind.trans (add_le_add hhide le_rfl)

/-- Batching multilinear extensions of fixed residual tables costs at most the number of row
variables plus one, divided by the field size. No union bound over the tables is needed. -/
theorem prob_MLE_affine_batch_eq_zero_le {F : Type} [Field F] [Fintype F] [SampleableType F]
    {n K : ℕ} (S : F) (rho : Fin K → (Fin n → Fin 2) → F)
    (hnontrivial : S ≠ 0 ∨ ∃ k u, rho k u ≠ 0) :
    Pr{let r ← $ᵗ ((Fin n → F) × (Fin K → F))}[
      S + ∑ k, MvPolynomial.eval r.1 (MvPolynomial.MLE (rho k)) * r.2 k = 0] ≤
      (n : ENNReal) / Fintype.card F + (Fintype.card F : ENNReal)⁻¹ := by
  apply prob_affine_batch_eq_zero_le S (fun k ↦ MvPolynomial.MLE (rho k))
  rcases hnontrivial with hS | ⟨k, u, hu⟩
  · exact Or.inl hS
  · refine Or.inr ⟨k, ?_, ?_⟩
    · intro hz
      exact hu ((MvPolynomial.MLE_eq_zero_iff (rho k)).mp hz u)
    · simpa using MvPolynomial.totalDegree_le_card_mul_of_mem_restrictDegree
        (MvPolynomial.MLE (rho k)) 1 (MvPolynomial.MLE_mem_restrictDegree (rho k))

end Probability

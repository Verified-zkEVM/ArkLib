/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.Polynomial.TaggedTuple
public import ArkLib.Data.Probability.Instances
public import ArkLib.Data.Finset.SumFiber

/-!
# Isolation bounds for typed tuple fingerprints

A selected semantic key is fixed before the challenge. Only collisions between it and the other
occurring keys are charged. The other keys may collide with one another. Consequently preserving
one nonzero fiber costs at most `(s-1)*W/|E|` for `s` distinct occurring keys, with no all-pairs
union bound. Weights can belong to any additive commutative monoid, including a challenge field.

These lemmas concern fixed input keys and weights. They do not permit either to adapt to the
fingerprint challenge and do not assert a complete native protocol security theorem.
-/

@[expose] public section

open OracleComp
open scoped ProbabilityTheory ENNReal

namespace TaggedTuple.Schema

variable {B E A ι : Type} {b W : ℕ}
variable [CommSemiring B] [Field E] [Fintype E] [SampleableType E]
variable [DecidableEq B]

/-- A fixed selected key collides with another listed key with probability at most
the number of other keys times the global fingerprint width divided by the challenge space. -/
theorem prob_not_isolated_le (schema : Schema B b W) (f : B →+* E)
    (hf : Function.Injective f) (keys : Finset schema.Key) (selected : schema.Key)
    (hselected : selected ∈ keys) :
    Pr{let beta ← $ᵗ E}[∃ k ∈ keys.erase selected,
      schema.fingerprint f beta k = schema.fingerprint f beta selected] ≤
        ((keys.card - 1) * W : ℕ) / (Fintype.card E : ℝ≥0∞) := by
  classical
  have hp : ∀ k ∈ keys, k ≠ selected → schema.polynomial f k ≠ schema.polynomial f selected := by
    intro k _ hne heq
    exact hne (schema.polynomial_injective f hf heq)
  simpa only [schema.eval_polynomial, Finset.card_erase_of_mem hselected] using
    Probability.prob_polynomial_eval_exists_eq_le keys (schema.polynomial f) selected hp
      (schema.natDegree_polynomial_le f selected)
      (fun k _ ↦ schema.natDegree_polynomial_le f k)

variable [DecidableEq E] [AddCommMonoid A]

/-- Compression can erase a selected nonzero fiber only when another occurring key collides
with it. The occurrence weights and selected key are fixed before the random challenge. -/
theorem prob_sumFiber_fingerprint_eq_zero_le (schema : Schema B b W) (f : B →+* E)
    (hf : Function.Injective f) (occ : Finset ι) (key : ι → schema.Key) (weight : ι → A)
    (selected : schema.Key) (hnonzero : occ.sumFiber key weight selected ≠ 0) :
    Pr{let beta ← $ᵗ E}[occ.sumFiber (schema.fingerprint f beta ∘ key) weight
      (schema.fingerprint f beta selected) = 0] ≤
        (((occ.image key).card - 1) * W : ℕ) / (Fintype.card E : ℝ≥0∞) := by
  have hselected : selected ∈ occ.image key := by
    by_contra h
    apply hnonzero
    apply Finset.sumFiber_eq_zero_of_forall_ne
    intro i hi heq
    exact h (Finset.mem_image.mpr ⟨i, hi, heq⟩)
  refine (prEvent_mono _ _ (fun beta ↦ ∃ k ∈ (occ.image key).erase selected,
    schema.fingerprint f beta k = schema.fingerprint f beta selected) ?_).trans
      (schema.prob_not_isolated_le f hf _ selected hselected)
  intro beta hzero
  by_contra hcollision
  have hisolated : ∀ i ∈ occ,
      schema.fingerprint f beta (key i) = schema.fingerprint f beta selected →
        key i = selected := by
    intro i hi heq
    by_contra hne
    exact hcollision ⟨key i, Finset.mem_erase.mpr
      ⟨hne, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩, heq⟩
  exact hnonzero ((Finset.sumFiber_comp_eq_of_isolated occ key weight
    (schema.fingerprint f beta) selected hisolated).symm.trans hzero)

/-- If some original fiber is nonzero, compression makes all fibers zero only
with the selected-key isolation error. One nonzero key is chosen before the challenge. -/
theorem prob_fingerprint_balanced_le (schema : Schema B b W) (f : B →+* E)
    (hf : Function.Injective f) (occ : Finset ι) (key : ι → schema.Key) (weight : ι → A)
    (hfalse : ∃ selected, occ.sumFiber key weight selected ≠ 0) :
    Pr{let beta ← $ᵗ E}[∀ encoded, occ.sumFiber (schema.fingerprint f beta ∘ key)
      weight encoded = 0] ≤
        (((occ.image key).card - 1) * W : ℕ) / (Fintype.card E : ℝ≥0∞) := by
  obtain ⟨selected, hselected⟩ := hfalse
  exact (prEvent_mono _ _ _ fun beta h ↦ h (schema.fingerprint f beta selected)).trans
    (schema.prob_sumFiber_fingerprint_eq_zero_le f hf occ key weight selected hselected)

end TaggedTuple.Schema

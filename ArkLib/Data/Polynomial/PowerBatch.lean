/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FiniteDomainQuotient
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Power batching of finite-domain zero tests

A family of polynomials is combined with successive powers of one scalar challenge. A false
family can vanish after batching only at roots of a nonzero challenge polynomial, giving error
at most `(k - 1) / |F|`. Evaluation is a weighted sum of the original evaluations, and batching
preserves their common degree budget. Computable polynomials implement the same operation.
-/

@[expose] public section

namespace Polynomial

variable {F : Type*} [Field F] {k d : ℕ}

/-- Combine a polynomial family using successive powers of a scalar challenge.
Mathlib polynomial arithmetic is noncomputable; `PowerBatch.batch` gives an executable model. -/
noncomputable def powerBatch (f : Fin k → F[X]) (α : F) : F[X] :=
  ∑ i, α ^ i.val • f i

/-- The virtual evaluation of a batch is the corresponding weighted sum. -/
theorem powerBatch_eval (f : Fin k → F[X]) (α ζ : F) :
    (powerBatch f α).eval ζ = ∑ i, α ^ i.val * (f i).eval ζ := by
  simp [powerBatch, eval_finsetSum, eval_smul, smul_eq_mul]

/-- Mapping a batch batches the mapped polynomials at the mapped challenge. -/
theorem powerBatch_map {E : Type*} [Field E] (f : Fin k → F[X]) (φ : F →+* E) (α : F) :
    (powerBatch f α).map φ = powerBatch (fun i => (f i).map φ) (φ α) := by
  simp [powerBatch, smul_eq_C_mul, Polynomial.map_sum]

/-- Batching preserves a strict degree budget, including the zero budget and empty family. -/
theorem degree_powerBatch_lt (f : Fin k → F[X]) (α : F) (d : ℕ)
    (hf : ∀ i, (f i).degree < d) : (powerBatch f α).degree < d := by
  rw [← mem_degreeLT]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem_degreeLT.mpr (hf i))

/-- Batching preserves vanishing on a finite domain for every challenge. -/
theorem zeroOn_powerBatch {S : Finset F} {f : Fin k → F[X]}
    (hf : ∀ i, ZeroOn S (f i)) (α : F) : ZeroOn S (powerBatch f α) := by
  intro ζ hζ
  simp [powerBatch_eval, fun i => hf i ζ hζ]

/-- Batching preserves an inclusive natural-degree budget. -/
theorem natDegree_powerBatch_le {f : Fin k → F[X]} (α : F)
    (hf : ∀ i, (f i).natDegree ≤ d) : (powerBatch f α).natDegree ≤ d := by
  exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_smul_le _ _).trans (hf i)

/-- Batching preserves a positive strict natural-degree budget, including for an empty family. -/
theorem natDegree_powerBatch_lt {f : Fin k → F[X]} (hd : 0 < d) (α : F)
    (hf : ∀ i, (f i).natDegree < d) : (powerBatch f α).natDegree < d := by
  exact lt_of_le_of_lt (natDegree_powerBatch_le α (fun i => Nat.le_pred_of_lt (hf i)))
    (Nat.pred_lt hd.ne')

variable [DecidableEq F]

/-- The polynomial in the challenge obtained by evaluating the family at one point. -/
def powerBatchChallenge (f : Fin k → F[X]) (ζ : F) : F[X] :=
  ofFn k (fun i => (f i).eval ζ)

/-- Evaluating the challenge polynomial agrees with evaluating the batch. -/
theorem powerBatchChallenge_eval (f : Fin k → F[X]) (ζ α : F) :
    (powerBatchChallenge f ζ).eval α = (powerBatch f α).eval ζ := by
  simp [powerBatchChallenge, ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial,
    powerBatch_eval, mul_comm]

/-- A nonzero evaluation in the family is a nonzero coefficient of the challenge polynomial. -/
theorem powerBatchChallenge_ne_zero {f : Fin k → F[X]} {ζ : F} {i : Fin k}
    (hi : (f i).eval ζ ≠ 0) : powerBatchChallenge f ζ ≠ 0 := by
  intro h
  apply hi
  simpa [powerBatchChallenge, i.isLt] using
    congrArg (fun p : F[X] => p.coeff i.val) h

/-- The challenge polynomial has degree at most one less than the family size. -/
theorem natDegree_powerBatchChallenge_le (f : Fin k → F[X]) (ζ : F) :
    (powerBatchChallenge f ζ).natDegree ≤ k - 1 := by
  by_cases hk : k = 0
  · subst k
    simp [powerBatchChallenge]
  · exact Nat.le_pred_of_lt (ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hk) _)

/-- A vanishing batch gives a root of the challenge polynomial at every domain point. -/
theorem zeroOn_powerBatch_subset_roots {S : Finset F} {f : Fin k → F[X]}
    {ζ : F} (hζ : ζ ∈ S) {α : F} (hα : ZeroOn S (powerBatch f α)) :
    (powerBatchChallenge f ζ).eval α = 0 := by
  rw [powerBatchChallenge_eval]
  exact hα ζ hζ

open ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-- A false family vanishes after uniform power batching with probability at most
`(k - 1) / |F|`. The entire family is fixed before sampling the challenge. -/
theorem prob_zeroOn_powerBatch_le {F : Type} [Field F]
    [Fintype F] [SampleableType F] {k : ℕ} {S : Finset F} {f : Fin k → F[X]}
    (hf : ¬ ∀ i, ZeroOn S (f i)) :
    Pr{let α ← $ᵗ F}[ZeroOn S (powerBatch f α)] ≤
      ((k - 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  classical
  simp only [ZeroOn, not_forall] at hf
  obtain ⟨i, ζ, hmem, hne⟩ := hf
  have hbound := Probability.prob_polynomial_eval_eq_le
    (powerBatchChallenge_ne_zero hne) (natDegree_powerBatchChallenge_le f ζ)
    (show (0 : F[X]).natDegree ≤ k - 1 by simp)
  refine le_trans ?_ hbound
  apply prEvent_mono ($ᵗ F) _ _
  intro α hα
  simpa using zeroOn_powerBatch_subset_roots hmem hα

end Polynomial

namespace PowerBatch

open CompPoly

variable (F : Type*) [Field F] [BEq F] [LawfulBEq F]

/-- A computable polynomial within a strict natural-degree budget. -/
abbrev Poly (d : ℕ) := {p : CPolynomial F // p.toPoly.natDegree < d}

variable {F} {d k : ℕ}

/-- Compute the power-weighted batch within the quotient zero test's polynomial budget. -/
def batch (hd : 0 < d) (f : Fin k → Poly F d) (α : F) :
    FiniteDomainQuotient.Poly F d :=
  ⟨∑ i, α ^ i.val • (f i).val, by
    rw [CPolynomial.toPoly_sum]
    simp only [CPolynomial.toPoly_smul]
    exact (Polynomial.natDegree_powerBatch_lt hd α (fun i => (f i).property)).le⟩

/-- The executable batch represents the mathematical power batch. -/
theorem batch_toPoly (hd : 0 < d) (f : Fin k → Poly F d) (α : F) :
    (batch hd f α).val.toPoly = Polynomial.powerBatch (fun i => (f i).val.toPoly) α := by
  simp [batch, Polynomial.powerBatch]

/-- The executable batch satisfies the same strict degree budget as its inputs. -/
theorem batch_natDegree_lt (hd : 0 < d) (f : Fin k → Poly F d) (α : F) :
    (batch hd f α).val.toPoly.natDegree < d := by
  rw [batch_toPoly]
  exact Polynomial.natDegree_powerBatch_lt hd α (fun i => (f i).property)

end PowerBatch

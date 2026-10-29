/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FiniteDomainQuotient
public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic

/-!
# Polynomial batching by zero-evading generators

A weighted sum preserves a family's common degree budget and vanishing domain. If one member
fails to vanish, its evaluations at a failing domain point form a nonzero vector. Vanishing of
the batch implies that the weights are orthogonal to this vector, so a zero-evading generator
bounds the probability of a false batch vanishing by its zero-evasion error.
-/

@[expose] public section

namespace Polynomial

variable {F : Type*} [Field F] {k d : ℕ}

/-- Combine a polynomial family with a vector of scalar weights.
`GeneratorBatch.batch` implements the same operation with computable polynomials. -/
noncomputable abbrev generatorBatch (f : Fin k → F[X]) (w : Fin k → F) : F[X] :=
  ∑ i, w i • f i

/-- Evaluation of a batch is the weighted sum of the original evaluations. -/
theorem generatorBatch_eval (f : Fin k → F[X]) (w : Fin k → F) (ζ : F) :
    (generatorBatch f w).eval ζ = ∑ i, w i * (f i).eval ζ := by
  simp [generatorBatch, eval_finsetSum, eval_smul, smul_eq_mul]

/-- Mapping a batch maps its polynomials and its scalar weights. -/
theorem generatorBatch_map {E : Type*} [Field E] (f : Fin k → F[X]) (φ : F →+* E)
    (w : Fin k → F) :
    (generatorBatch f w).map φ = generatorBatch (fun i => (f i).map φ) (φ ∘ w) := by
  simp [generatorBatch, smul_eq_C_mul, Polynomial.map_sum]

/-- A weighted sum preserves a strict degree budget. -/
theorem degree_generatorBatch_lt (f : Fin k → F[X]) (w : Fin k → F) (d : ℕ)
    (hf : ∀ i, (f i).degree < d) : (generatorBatch f w).degree < d := by
  rw [← mem_degreeLT]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem_degreeLT.mpr (hf i))

/-- Every weighted sum of polynomials vanishing on a domain also vanishes there. -/
theorem zeroOn_generatorBatch {H : Finset F} {f : Fin k → F[X]}
    (hf : ∀ i, ZeroOn H (f i)) (w : Fin k → F) : ZeroOn H (generatorBatch f w) := by
  intro ζ hζ
  simp [generatorBatch_eval, fun i => hf i ζ hζ]

/-- A weighted sum preserves an inclusive natural-degree budget. -/
theorem natDegree_generatorBatch_le {f : Fin k → F[X]} (w : Fin k → F)
    (hf : ∀ i, (f i).natDegree ≤ d) : (generatorBatch f w).natDegree ≤ d := by
  exact natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_smul_le _ _).trans (hf i)

/-- A weighted sum preserves a positive strict natural-degree budget, even for an empty family. -/
theorem natDegree_generatorBatch_lt {f : Fin k → F[X]} (hd : 0 < d) (w : Fin k → F)
    (hf : ∀ i, (f i).natDegree < d) : (generatorBatch f w).natDegree < d := by
  exact lt_of_le_of_lt (natDegree_generatorBatch_le w (fun i => Nat.le_pred_of_lt (hf i)))
    (Nat.pred_lt hd.ne')

/-- Vanishing of the batch forces its weights to be orthogonal to the evaluation vector
at each point of the vanishing domain. -/
theorem zeroOn_generatorBatch_dotProduct {H : Finset F} {f : Fin k → F[X]}
    {w : Fin k → F} {ζ : F} (hζ : ζ ∈ H) (h : ZeroOn H (generatorBatch f w)) :
    dotProduct w (fun i => (f i).eval ζ) = 0 := by
  simpa only [generatorBatch_eval, dotProduct] using h ζ hζ

open ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-- A pointwise zero-evasion bound bounds the probability that a false family vanishes
when batched. The family is fixed before the uniform seed is drawn. -/
theorem prob_zeroOn_generatorBatch_le_of_pointwise {F S : Type} [Field F]
    [Nonempty S] [SampleableType S] {k : ℕ}
    (G : CoreDefinitions.Generator S (Fin k) F) {ε : ℝ≥0∞}
    (hG : ∀ v : Fin k → F, v ≠ 0 →
      Pr{let s ← $ᵗ S}[dotProduct (G s) v = 0] ≤ ε)
    {H : Finset F} {f : Fin k → F[X]} (hf : ¬ ∀ i, ZeroOn H (f i)) :
    Pr{let s ← $ᵗ S}[ZeroOn H (generatorBatch f (G s))] ≤ ε := by
  classical
  simp only [ZeroOn, not_forall] at hf
  obtain ⟨i, ζ, hmem, hne⟩ := hf
  have hv : (fun j => (f j).eval ζ) ≠ 0 := by
    intro h
    exact hne (congrFun h i)
  refine le_trans ?_ (hG _ hv)
  exact prEvent_mono ($ᵗ S) _ _ fun s hs => zeroOn_generatorBatch_dotProduct hmem hs

/-- A zero-evading generator batches any fixed false family with error at most its
zero-evasion error. -/
theorem prob_zeroOn_generatorBatch_le {F S : Type} [Field F]
    [Fintype S] [Nonempty S] [SampleableType S] {k : ℕ}
    (G : CoreDefinitions.Generator S (Fin k) F) {ε : unitInterval}
    (hG : CoreDefinitions.IsZeroEvadingGenerator G ε)
    {H : Finset F} {f : Fin k → F[X]} (hf : ¬ ∀ i, ZeroOn H (f i)) :
    Pr{let s ← $ᵗ S}[ZeroOn H (generatorBatch f (G s))] ≤ ENNReal.ofReal ε := by
  refine prob_zeroOn_generatorBatch_le_of_pointwise G (fun v hv => ?_) hf
  unfold CoreDefinitions.IsZeroEvadingGenerator at hG
  exact le_trans (le_sSup (show Pr{let s ← $ᵗ S}[dotProduct (G s) v = 0] ∈
    {y | ∃ u : Fin k → F, u ≠ 0 ∧ y = Pr{let s ← $ᵗ S}[dotProduct (G s) u = 0]} from
      ⟨v, hv, rfl⟩)) hG

end Polynomial

namespace GeneratorBatch

open CompPoly

variable (F : Type*) [Field F] [BEq F] [LawfulBEq F]

/-- A computable polynomial within a strict natural-degree budget. -/
abbrev Poly (d : ℕ) := {p : CPolynomial F // p.toPoly.natDegree < d}

variable {F} {d k : ℕ}

/-- Compute a weighted batch within the quotient zero test's polynomial budget. -/
abbrev batch (hd : 0 < d) (f : Fin k → Poly F d) (w : Fin k → F) :
    FiniteDomainQuotient.Poly F d :=
  ⟨∑ i, w i • (f i).val, by
    rw [CPolynomial.toPoly_sum]
    simp only [CPolynomial.toPoly_smul]
    exact (Polynomial.natDegree_generatorBatch_lt hd w (fun i => (f i).property)).le⟩

/-- The executable batch represents the mathematical weighted batch. -/
theorem batch_toPoly (hd : 0 < d) (f : Fin k → Poly F d) (w : Fin k → F) :
    (batch hd f w).val.toPoly = Polynomial.generatorBatch (fun i => (f i).val.toPoly) w := by
  simp [Polynomial.generatorBatch]

/-- The executable batch satisfies the same strict degree budget as its inputs. -/
theorem batch_natDegree_lt (hd : 0 < d) (f : Fin k → Poly F d) (w : Fin k → F) :
    (batch hd f w).val.toPoly.natDegree < d := by
  rw [batch_toPoly]
  exact Polynomial.natDegree_generatorBatch_lt hd w (fun i => (f i).property)

end GeneratorBatch

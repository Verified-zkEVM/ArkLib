/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.GeneratorBatch
public import ArkLib.Data.CodingTheory.ProximityGenerator.ZeroEvading

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
  generatorBatch f (fun i => α ^ i.val)

/-- The virtual evaluation of a batch is the corresponding weighted sum. -/
theorem powerBatch_eval (f : Fin k → F[X]) (α ζ : F) :
    (powerBatch f α).eval ζ = ∑ i, α ^ i.val * (f i).eval ζ := by
  exact generatorBatch_eval f _ ζ

/-- Mapping a batch batches the mapped polynomials at the mapped challenge. -/
theorem powerBatch_map {E : Type*} [Field E] (f : Fin k → F[X]) (φ : F →+* E) (α : F) :
    (powerBatch f α).map φ = powerBatch (fun i => (f i).map φ) (φ α) := by
  simpa only [powerBatch, Function.comp_def, map_pow] using
    generatorBatch_map f φ (fun i => α ^ i.val)

/-- Batching preserves a strict degree budget, including the zero budget and empty family. -/
theorem degree_powerBatch_lt (f : Fin k → F[X]) (α : F) (d : ℕ)
    (hf : ∀ i, (f i).degree < d) : (powerBatch f α).degree < d := by
  exact degree_generatorBatch_lt f _ d hf

/-- Batching preserves vanishing on a finite domain for every challenge. -/
theorem zeroOn_powerBatch {S : Finset F} {f : Fin k → F[X]}
    (hf : ∀ i, ZeroOn S (f i)) (α : F) : ZeroOn S (powerBatch f α) := by
  exact zeroOn_generatorBatch hf _

/-- Batching preserves an inclusive natural-degree budget. -/
theorem natDegree_powerBatch_le {f : Fin k → F[X]} (α : F)
    (hf : ∀ i, (f i).natDegree ≤ d) : (powerBatch f α).natDegree ≤ d := by
  exact natDegree_generatorBatch_le _ hf

/-- Batching preserves a positive strict natural-degree budget, including for an empty family. -/
theorem natDegree_powerBatch_lt {f : Fin k → F[X]} (hd : 0 < d) (α : F)
    (hf : ∀ i, (f i).natDegree < d) : (powerBatch f α).natDegree < d := by
  exact natDegree_generatorBatch_lt hd _ hf

open ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-- A false family vanishes after uniform power batching with probability at most
`(k - 1) / |F|`. The entire family is fixed before sampling the challenge. -/
theorem prob_zeroOn_powerBatch_le {F : Type} [Field F]
    [Fintype F] [SampleableType F] {k : ℕ} {S : Finset F} {f : Fin k → F[X]}
    (hf : ¬ ∀ i, ZeroOn S (f i)) :
    Pr{let α ← $ᵗ F}[ZeroOn S (powerBatch f α)] ≤
      ((k - 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  exact prob_zeroOn_generatorBatch_le_of_pointwise
    (CoreDefinitions.powerBatchGenerator F k)
    (fun v hv => CoreDefinitions.prob_dotProduct_powerBatchGenerator_eq_zero_le v hv) hf

end Polynomial

namespace PowerBatch

open CompPoly

variable (F : Type*) [Field F] [BEq F] [LawfulBEq F]

/-- A computable polynomial within a strict natural-degree budget. -/
abbrev Poly (d : ℕ) := GeneratorBatch.Poly F d

variable {F} {d k : ℕ}

/-- Compute the power-weighted batch within the quotient zero test's polynomial budget. -/
abbrev batch (hd : 0 < d) (f : Fin k → Poly F d) (α : F) :
    FiniteDomainQuotient.Poly F d :=
  GeneratorBatch.batch hd f (fun i => α ^ i.val)

/-- The executable batch represents the mathematical power batch. -/
theorem batch_toPoly (hd : 0 < d) (f : Fin k → Poly F d) (α : F) :
    (batch hd f α).val.toPoly = Polynomial.powerBatch (fun i => (f i).val.toPoly) α := by
  exact GeneratorBatch.batch_toPoly hd f _

/-- The executable batch satisfies the same strict degree budget as its inputs. -/
theorem batch_natDegree_lt (hd : 0 < d) (f : Fin k → Poly F d) (α : F) :
    (batch hd f α).val.toPoly.natDegree < d := by
  exact GeneratorBatch.batch_natDegree_lt hd f _

end PowerBatch

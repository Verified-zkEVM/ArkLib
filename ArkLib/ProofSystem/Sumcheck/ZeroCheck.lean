/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ProofSystem.Sumcheck.Batching

/-!
# Zero-check claims

This file defines the algebraic claims used to batch polynomial constraints, reduce their vanishing
on a Boolean hypercube to sum-check, and merge claims whose cubes have different dimensions. Shorter
claims use a suffix of the shared point; the unused prefix variables contribute a product selector.

The declarations here describe claims and error budgets. Protocol security is inherited only after
the corresponding claims are connected to committed polynomial oracles.

## References

* [Lund, C., Fortnow, L., Karloff, H., and Nisan, N., *Algebraic methods for interactive
    proof systems*][LFKN92]
-/

noncomputable section

open MvPolynomial
open scoped BigOperators NNReal

namespace Sumcheck.ZeroCheck

/-- Algebraic data for one constraint table. -/
structure Table (R : Type) where
  /-- The number of variables, so the table has `2 ^ height` Boolean rows. -/
  height : ℕ
  /-- The number of polynomial constraints. -/
  constraintCount : ℕ
  /-- A constraint after substituting the table's column polynomials. -/
  constraint : Fin constraintCount → (Fin height → R) → R
  /-- The number of attached polynomial-evaluation claims. -/
  evaluationCount : ℕ
  /-- An attached polynomial expression. -/
  evaluation : Fin evaluationCount → (Fin height → R) → R
  /-- The advertised value of an attached polynomial expression. -/
  claimedValue : Fin evaluationCount → R

/-- An ordered family of constraint tables. The order fixes the global batching powers. -/
structure Family (R : Type) (tableCount : ℕ) where
  /-- The tables in the family. -/
  table : Fin tableCount → Table R

namespace Family

variable {R : Type} [CommSemiring R] {tableCount : ℕ}

/-- The global offset of the first constraint belonging to table `t`. -/
def constraintOffset (family : Family R tableCount) (t : Fin tableCount) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin tableCount ↦ u < t),
    (family.table u).constraintCount

/-- The total number of constraints in the family. -/
def totalConstraintCount (family : Family R tableCount) : ℕ :=
  ∑ t, (family.table t).constraintCount

/-- The global offset of table `t`'s attached evaluation claims. -/
def evaluationOffset (family : Family R tableCount) (t : Fin tableCount) : ℕ :=
  family.totalConstraintCount +
    ∑ u ∈ Finset.univ.filter (fun u : Fin tableCount ↦ u < t),
      (family.table u).evaluationCount

/-- The total number of entries in the batching polynomial. -/
def totalBatchCount (family : Family R tableCount) : ℕ :=
  family.totalConstraintCount + ∑ t, (family.table t).evaluationCount

/-- The random linear combination of table `t`'s constraints. -/
def batchedConstraints (family : Family R tableCount) (ρ : R)
    (t : Fin tableCount) (x : Fin (family.table t).height → R) : R :=
  ∑ k : Fin (family.table t).constraintCount,
    ρ ^ (family.constraintOffset t + (k : ℕ)) * (family.table t).constraint k x

/-- The random linear combination of table `t`'s attached evaluation polynomials. -/
def batchedEvaluations (family : Family R tableCount) (ρ : R)
    (t : Fin tableCount) (x : Fin (family.table t).height → R) : R :=
  ∑ j : Fin (family.table t).evaluationCount,
    ρ ^ (family.evaluationOffset t + (j : ℕ)) * (family.table t).evaluation j x

/-- The complete batched polynomial value for table `t`. -/
def batchedValue (family : Family R tableCount) (ρ : R)
    (t : Fin tableCount) (x : Fin (family.table t).height → R) : R :=
  family.batchedConstraints ρ t x + family.batchedEvaluations ρ t x

/-- The target shift contributed by table `t`'s attached evaluation claims. -/
def tableTarget (family : Family R tableCount) (ρ : R) (t : Fin tableCount) : R :=
  ∑ j : Fin (family.table t).evaluationCount,
    ρ ^ (family.evaluationOffset t + (j : ℕ)) * (family.table t).claimedValue j

end Family

variable {R : Type} [Field R] {tableCount : ℕ}

/-- The per-table claim
`∑ b, eqTilde b r * f b = target`, where `f` is the batched constraint polynomial. -/
def tableClaim (family : Family R tableCount) (ρ : R) (t : Fin tableCount)
    (r : Fin (family.table t).height → R) : Batching.Claim R (family.table t).height where
  summand x := eqTilde x r * family.batchedValue ρ t x
  target := family.tableTarget ρ t

/-- The semantic input relation for a per-table zero-check sum-check. -/
def inputRelation {degree : ℕ} (family : Family R tableCount) (ρ : R)
    (t : Fin tableCount) (r : Fin (family.table t).height → R) :=
  (tableClaim family ρ t r).relation (degree := degree) (boolEmbedding R)

/-- The length-`h` suffix of a length-`hMax` point. -/
def suffix {h hMax : ℕ} (x : Fin hMax → R) (hle : h ≤ hMax) : Fin h → R :=
  fun i ↦ x ⟨hMax - h + i, by omega⟩

/-- The product of the `hMax - h` unused prefix variables. -/
def prefixProduct {h hMax : ℕ} (x : Fin hMax → R) (hle : h ≤ hMax) : R :=
  ∏ i : Fin (hMax - h), x ⟨i, by omega⟩

omit [Field R] in
@[simp]
theorem suffix_self {h : ℕ} (x : Fin h → R) : suffix x (le_refl h) = x := by
  funext i
  simp [suffix]

@[simp]
theorem prefixProduct_self {h : ℕ} (x : Fin h → R) :
    prefixProduct x (le_refl h) = 1 := by
  simp only [prefixProduct]
  apply Finset.prod_eq_one
  intro i _
  have hi : (i : ℕ) < h - h := i.isLt
  omega

/-- One table's summand inside a merged, back-loaded zero-check claim. -/
def mergedTableTerm (family : Family R tableCount) (ρ : R) (hMax : ℕ)
    (height_le : ∀ t, (family.table t).height ≤ hMax) (r x : Fin hMax → R)
    (t : Fin tableCount) : R :=
  let xT := suffix x (height_le t)
  let rT := suffix r (height_le t)
  prefixProduct x (height_le t) * eqTilde xT rT * family.batchedValue ρ t xT

/-- The single, back-loaded sum-check claim merging all table zero checks. -/
def mergedClaim (family : Family R tableCount) (ρ : R) (hMax : ℕ)
    (height_le : ∀ t, (family.table t).height ≤ hMax) (r : Fin hMax → R) :
    Batching.Claim R hMax where
  summand x := ∑ t, mergedTableTerm family ρ hMax height_le r x t
  target := ∑ t, family.tableTarget ρ t

/-- The semantic input relation for the merged, back-loaded zero-check sum-check. -/
def mergedInputRelation {degree : ℕ} (family : Family R tableCount) (ρ : R)
    (hMax : ℕ) (height_le : ∀ t, (family.table t).height ≤ hMax)
    (r : Fin hMax → R) :=
  (mergedClaim family ρ hMax height_le r).relation (degree := degree) (boolEmbedding R)

/-- The constraint-batching error `N / |R|`. -/
def constraintBatchingError [Fintype R] (family : Family R tableCount) : ℝ≥0 :=
  family.totalConstraintCount / Fintype.card R

/-- The batching error including attached evaluation claims. -/
def batchingError [Fintype R] (family : Family R tableCount) : ℝ≥0 :=
  family.totalBatchCount / Fintype.card R

/-- The zero-check interpolation error `h / |R|`. -/
def interpolationError [Fintype R] (h : ℕ) : ℝ≥0 :=
  h / Fintype.card R

/-- The standard `h`-round sum-check error for individual degree at most `degree`. -/
def sumcheckError [Fintype R] (h degree : ℕ) : ℝ≥0 :=
  (h * degree) / Fintype.card R

/-- The combined interpolation and sum-check error `h * (degree + 1) / |R|`. -/
def totalError [Fintype R] (h degree : ℕ) : ℝ≥0 :=
  (h * (degree + 1)) / Fintype.card R

end Sumcheck.ZeroCheck

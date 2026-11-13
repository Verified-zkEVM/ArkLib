/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Evaluation.Relation
public import ArkLib.Data.Probability.Instances

/-!
# Independent batching of Spartan row claims

The second sumcheck claims the independent linear combination of the three row values.
A false vector of claims survives precisely when its fixed error vector is orthogonal to the
sampled coefficients.
-/

@[expose] public section

instance R1CS.MatrixIdx.instFintype : Fintype R1CS.MatrixIdx :=
  ⟨{.A, .B, .C}, fun i => by cases i <;> simp⟩

/-- The three matrix labels have a computable enumeration for independent sampling. -/
instance R1CS.MatrixIdx.instFinEnum : FinEnum R1CS.MatrixIdx :=
  FinEnum.ofNodupList [.A, .B, .C] (fun i => by cases i <;> simp) (by decide)

namespace Spartan.Batching

open MvPolynomial Realization
open scoped BigOperators

variable {R : Type} [CommRing R] (pp : PublicParams)

/-- The claimed sum for the second sumcheck. -/
def batchedClaim (ρ v : R1CS.MatrixIdx → R) : R := ∑ i, ρ i * v i

/-- Form the second sumcheck statement from the sampled coefficients. -/
def batch (s : InputStatement (R := R) pp) (ρ : R1CS.MatrixIdx → R) :
    Statement (R := R) pp := ⟨s, ρ, batchedClaim ρ s.1⟩

/-- The second virtual polynomial's Boolean sum equals the public claimed sum. -/
def outputRelation (s : Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) : Prop :=
  Algebra.cubeSum (Algebra.secondVirtual (fun i => o (.inl i))
    (R1CS.𝕫 s.input.2.x (o (.inr 0))) s.input.2.r_x s.ρ) = s.c

/-- The Boolean sum of the second virtual polynomial batches the true row values. -/
theorem cubeSum_eq_batchedClaim (s : Evaluation.Statement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) (ρ : R1CS.MatrixIdx → R) :
    Algebra.cubeSum (Algebra.secondVirtual (fun i => o (.inl i))
      (R1CS.𝕫 s.x (o (.inr 0))) s.r_x ρ) =
      batchedClaim ρ (Evaluation.values pp s o) := by
  calc
    _ = _ := Algebra.secondVirtual_cubeSum_eq (m := pp.ℓ_m) (n := pp.ℓ_n)
      (fun i => o (.inl i)) (R1CS.𝕫 s.x (o (.inr 0))) s.r_x ρ
    _ = _ := by
      have h (i : R1CS.MatrixIdx) := rowEval_eq (m := pp.ℓ_m) (n := pp.ℓ_n)
        (o (.inl i)) (R1CS.𝕫 s.x (o (.inr 0))) s.r_x
      simp only [batchedClaim, Evaluation.values]
      change _ = ∑ i ∈ ({.A, .B, .C} : Finset R1CS.MatrixIdx),
        ρ i * rowEval (o (.inl i)) (R1CS.𝕫 s.x (o (.inr 0))) s.r_x
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
        reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton, h, add_assoc]

/-- True row claims give the second sumcheck's claimed Boolean sum. -/
theorem batchedClaim_complete (s : InputStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) (ρ : R1CS.MatrixIdx → R)
    (h : Evaluation.outputRelation pp s.2 o s.1) :
    outputRelation pp (batch pp s ρ) o := by
  have hv : s.1 = Evaluation.values pp s.2 o := by
    funext i
    exact (h i).trans (rowEval_eq _ _ _).symm
  change Algebra.cubeSum _ = batchedClaim ρ s.1
  rw [cubeSum_eq_batchedClaim, hv]
  rfl

/-- The error vector is fixed by the input statement and retained oracle tables. -/
def errorVector (s : InputStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) : R1CS.MatrixIdx → R :=
  fun i => s.1 i - Evaluation.values pp s.2 o i

/-- False row claims have a nonzero error vector. -/
theorem errorVector_ne_zero (s : InputStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i)
    (h : ¬ Evaluation.outputRelation pp s.2 o s.1) : errorVector pp s o ≠ 0 := by
  intro heq
  apply h
  intro i
  have hi := congrFun heq i
  simp only [errorVector, Pi.zero_apply, sub_eq_zero] at hi
  exact hi.trans (rowEval_eq _ _ _)

/-- Acceptance of a batched claim is exactly collision of the fixed error vector. -/
theorem outputRelation_iff_collision (s : InputStatement (R := R) pp)
    (o : ∀ i, OracleStatement (R := R) pp i) (ρ : R1CS.MatrixIdx → R) :
    outputRelation pp (batch pp s ρ) o ↔ ∑ i, ρ i * errorVector pp s o i = 0 := by
  change Algebra.cubeSum _ = batchedClaim ρ s.1 ↔ _
  rw [cubeSum_eq_batchedClaim]
  simp only [errorVector, mul_sub, Finset.sum_sub_distrib, sub_eq_zero, batchedClaim]
  exact eq_comm

/-- For any false input vector, exactly one field-cardinality fraction of batches are true. -/
theorem independent_batch_collision_eq_inv_card
    {F : Type} [Field F] [Fintype F] [SampleableType F]
    (s : InputStatement (R := F) pp)
    (o : ∀ i, OracleStatement (R := F) pp i)
    (h : ¬ Evaluation.outputRelation pp s.2 o s.1) :
    Pr{let ρ ← $ᵗ (R1CS.MatrixIdx → F)}[outputRelation pp (batch pp s ρ) o] =
      1 / (Fintype.card F : ENNReal) := by
  simp_rw [outputRelation_iff_collision]
  simpa only [one_div, mul_comm] using Probability.prob_dotProduct_eq_zero_eq_inv_card
    (errorVector pp s o) (errorVector_ne_zero pp s o h)

end Spartan.Batching

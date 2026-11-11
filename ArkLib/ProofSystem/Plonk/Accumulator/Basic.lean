/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Relation.PermutationFingerprint
public import ArkLib.ProofSystem.Plonk.Encoding.Basic
public import ArkLib.Data.Finset.CyclicProduct
public import ArkLib.Data.Polynomial.AffineFactorBadChallenge
public import Mathlib.Algebra.Polynomial.BigOperators

/-! # Cyclic Plonk accumulators

The numerator and denominator encode the two labeled products. Normalized cyclic recurrence
forces their products to agree, even when factors vanish.
-/

@[expose] public section

namespace Plonk

open Polynomial
open scoped BigOperators

variable {F : Type} [Field F] {m n : ℕ}

/-- The numerator product, using Mathlib's noncomputable polynomial arithmetic. -/
noncomputable def accumulatorNumerator (a : Fin 3 → degreeLT F n)
    (k : Fin 3 → F) (β γ : F) : F[X] :=
  ∏ c, ((a c).val + C (β * k c) * X + C γ)

/-- The denominator product, using Mathlib's noncomputable polynomial arithmetic. -/
noncomputable def accumulatorDenominator (a s : Fin 3 → degreeLT F n)
    (β γ : F) : F[X] :=
  ∏ c, ((a c).val + C β * (s c).val + C γ)

@[simp]
theorem eval_accumulatorNumerator (a : Fin 3 → degreeLT F n)
    (k : Fin 3 → F) (β γ x : F) :
    (accumulatorNumerator a k β γ).eval x =
      ∏ c, ((a c).val.eval x + β * k c * x + γ) := by
  simp [accumulatorNumerator, eval_prod]

@[simp]
theorem eval_accumulatorDenominator (a s : Fin 3 → degreeLT F n) (β γ x : F) :
    (accumulatorDenominator a s β γ).eval x =
      ∏ c, ((a c).val.eval x + β * (s c).val.eval x + γ) := by
  simp [accumulatorDenominator, eval_prod]

/-- Normalization and the multiplication-form recurrence at every domain node. -/
def AccumulatorRelation (D : EvaluationDomain F n) (ω : F) (N Q Z : F[X]) : Prop :=
  Z.eval 1 = 1 ∧ ∀ i, Z.eval (ω * D.node i) * Q.eval (D.node i) =
    Z.eval (D.node i) * N.eval (D.node i)

/-- The difference of the domain products is the labeled permutation fingerprint. -/
theorem accumulator_products_sub_eq_fingerprint (D : EvaluationDomain F n)
    (cs : ConstraintSystem F m n) (L : CosetLabels D)
    (a : Fin 3 → degreeLT F n) (β γ : F) :
    (∏ i, (accumulatorNumerator a L.multiplier β γ).eval (D.node i)) -
      (∏ i, (accumulatorDenominator a (permutationPolynomials D cs L.label)
        β γ).eval (D.node i)) =
      PermutationFingerprint.fingerprint (polynomialOccurrences D a)
        L.labelEmbedding cs.perm β γ := by
  have reindex (f : Fin (3 * n) → F) :
      (∏ i : Fin n, ∏ c : Fin 3, f (finProdFinEquiv (c, i))) = ∏ p, f p := by
    rw [Finset.prod_comm]
    calc
      _ = ∏ p : Fin 3 × Fin n, f (finProdFinEquiv p) :=
        (Fintype.prod_prod_type _).symm
      _ = _ := Equiv.prod_comp finProdFinEquiv f
  unfold PermutationFingerprint.fingerprint
  congr 1
  · rw [← reindex]
    apply Finset.prod_congr rfl
    intro i _
    simp [CosetLabels.columnLabel, mul_assoc]
  · rw [← reindex]
    apply Finset.prod_congr rfl
    intro i _
    simp

/-- Copy constraints give equality of the numerator and denominator domain products. -/
theorem accumulator_products_eq_of_copy (D : EvaluationDomain F n)
    (cs : ConstraintSystem F m n) (L : CosetLabels D)
    (a : Fin 3 → degreeLT F n)
    (ha : cs.CopyConstraintsSatisfied (polynomialOccurrences D a)) (β γ : F) :
    (∏ i, (accumulatorNumerator a L.multiplier β γ).eval (D.node i)) =
      ∏ i, (accumulatorDenominator a (permutationPolynomials D cs L.label)
        β γ).eval (D.node i) := by
  apply sub_eq_zero.mp
  rw [accumulator_products_sub_eq_fingerprint]
  exact cs.fingerprint_eq_zero_of_copyConstraints L _ ha β γ

/-- The cyclic polynomial recurrence forces equality of the whole products without division. -/
theorem accumulator_products_eq (ω : F) (hω : IsPrimitiveRoot ω n) (N Q Z : F[X])
    (hZ : AccumulatorRelation (EvaluationDomain.primitiveRoot ω hω) ω N Q Z) :
    (∏ i : Fin n, N.eval (ω ^ (i : ℕ))) = ∏ i : Fin n, Q.eval (ω ^ (i : ℕ)) := by
  suffices h : (∏ i ∈ Finset.range n, N.eval (ω ^ i)) =
      ∏ i ∈ Finset.range n, Q.eval (ω ^ i) by
    simpa only [Finset.prod_range] using h
  apply CyclicProduct.products_eq _ _ (fun i => Z.eval (ω ^ i)) n
  · simpa using hZ.1
  · intro i hi
    simpa [EvaluationDomain.primitiveRoot_node, pow_succ', mul_comm] using hZ.2 ⟨i, hi⟩
  · simpa [hω.pow_eq_one] using hZ.1

/-- Any normalized accumulator makes the permutation fingerprint vanish. -/
theorem fingerprint_eq_zero_of_accumulator (ω : F) (hω : IsPrimitiveRoot ω n)
    (cs : ConstraintSystem F m n) (L : CosetLabels (EvaluationDomain.primitiveRoot ω hω))
    (a : Fin 3 → degreeLT F n) (β γ : F) (Z : F[X])
    (hZ : AccumulatorRelation (EvaluationDomain.primitiveRoot ω hω) ω
      (accumulatorNumerator a L.multiplier β γ)
      (accumulatorDenominator a
        (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ) Z) :
    PermutationFingerprint.fingerprint
      (polynomialOccurrences (EvaluationDomain.primitiveRoot ω hω) a)
      L.labelEmbedding cs.perm β γ = 0 := by
  rw [← accumulator_products_sub_eq_fingerprint]
  exact sub_eq_zero.mpr (accumulator_products_eq ω hω _ _ _ hZ)

/-- Interpolate the ratio prefixes. Mathlib's polynomial interpolation is noncomputable. -/
noncomputable def honestAccumulator (ω : F) (hω : IsPrimitiveRoot ω n) (N Q : F[X]) :
    degreeLT F n :=
  (EvaluationDomain.primitiveRoot ω hω).interpolate
    (fun i => CyclicProduct.ratioPrefix (fun j => N.eval (ω ^ j))
      (fun j => Q.eval (ω ^ j)) i.val)

@[simp]
theorem eval_honestAccumulator (ω : F) (hω : IsPrimitiveRoot ω n) (N Q : F[X])
    (i : Fin n) :
    (honestAccumulator ω hω N Q).val.eval (ω ^ i.val) =
      CyclicProduct.ratioPrefix (fun j => N.eval (ω ^ j)) (fun j => Q.eval (ω ^ j)) i.val :=
  EvaluationDomain.eval_interpolate (EvaluationDomain.primitiveRoot ω hω) _ i

/-- Nonzero denominators and equal total products give an honest normalized accumulator. -/
theorem honestAccumulator_relation (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 0 < n)
    (N Q : F[X]) (hQ : ∀ i : Fin n, Q.eval (ω ^ i.val) ≠ 0)
    (heq : (∏ i : Fin n, N.eval (ω ^ i.val)) = ∏ i : Fin n, Q.eval (ω ^ i.val)) :
    AccumulatorRelation (EvaluationDomain.primitiveRoot ω hω) ω N Q
      (honestAccumulator ω hω N Q).val := by
  have hzero : (honestAccumulator ω hω N Q).val.eval 1 = 1 := by
    simpa using eval_honestAccumulator ω hω N Q ⟨0, hn⟩
  refine ⟨hzero, ?_⟩
  intro i
  have hnext : (honestAccumulator ω hω N Q).val.eval (ω ^ (i.val + 1)) =
      CyclicProduct.ratioPrefix (fun j => N.eval (ω ^ j))
        (fun j => Q.eval (ω ^ j)) (i.val + 1) := by
    by_cases hi : i.val + 1 < n
    · exact eval_honestAccumulator ω hω N Q ⟨i.val + 1, hi⟩
    · have hi : i.val + 1 = n := by omega
      rw [hi, hω.pow_eq_one, hzero]
      symm
      apply CyclicProduct.ratioPrefix_end
      · intro j hj
        exact hQ ⟨j, hj⟩
      · simpa only [Finset.prod_range] using heq
  change (honestAccumulator ω hω N Q).val.eval (ω * ω ^ i.val) * _ = _
  simp only [EvaluationDomain.primitiveRoot_node]
  rw [← pow_succ', hnext, eval_honestAccumulator]
  exact CyclicProduct.ratioPrefix_recurrence _ _ i.val (hQ i)

/-- The denominator has a zero column factor at some row. -/
def BadChallenge (D : EvaluationDomain F n) (a s : Fin 3 → degreeLT F n)
    (β γ : F) : Prop :=
  ∃ c i, (a c).val.eval (D.node i) + β * (s c).val.eval (D.node i) + γ = 0

/-- Outside the explicit bad set every row denominator is nonzero. -/
theorem accumulatorDenominator_ne_zero (D : EvaluationDomain F n)
    (a s : Fin 3 → degreeLT F n) (β γ : F) (hgood : ¬ BadChallenge D a s β γ)
    (i : Fin n) : (accumulatorDenominator a s β γ).eval (D.node i) ≠ 0 := by
  rw [eval_accumulatorDenominator]
  apply Finset.prod_ne_zero_iff.mpr
  intro c _ hc
  exact hgood ⟨c, i, hc⟩

open scoped ProbabilityTheory NNReal in
/-- At most `3n / |F|` of joint uniform challenges have a zero denominator factor. -/
theorem prob_badChallenge_le [Fintype F] [SampleableType F]
    (D : EvaluationDomain F n) (a s : Fin 3 → degreeLT F n) :
    Pr{let r ← $ᵗ (F × F)}[BadChallenge D a s r.1 r.2] ≤
      (((3 * n : ℕ) : ℝ≥0) / Fintype.card F : ℝ≥0) := by
  have h := AffineFactorBadChallenge.prob_badChallenge_le
    (fun p : Fin 3 × Fin n => (a p.1).val.eval (D.node p.2))
    (fun p : Fin 3 × Fin n => (s p.1).val.eval (D.node p.2))
  simpa [AffineFactorBadChallenge.BadChallenge, BadChallenge] using h

/-- Copy-consistent columns admit the honest accumulator outside the zero-factor bad set. -/
theorem honestAccumulator_relation_of_copy (ω : F) (hω : IsPrimitiveRoot ω n)
    (hn : 0 < n) (cs : ConstraintSystem F m n)
    (L : CosetLabels (EvaluationDomain.primitiveRoot ω hω))
    (a : Fin 3 → degreeLT F n) (β γ : F)
    (ha : cs.CopyConstraintsSatisfied
      (polynomialOccurrences (EvaluationDomain.primitiveRoot ω hω) a))
    (hgood : ¬ BadChallenge (EvaluationDomain.primitiveRoot ω hω) a
      (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ) :
    let N := accumulatorNumerator a L.multiplier β γ
    let Q := accumulatorDenominator a
      (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ
    AccumulatorRelation (EvaluationDomain.primitiveRoot ω hω) ω N Q
      (honestAccumulator ω hω N Q).val := by
  apply honestAccumulator_relation ω hω hn
  · exact accumulatorDenominator_ne_zero _ _ _ β γ hgood
  · exact accumulator_products_eq_of_copy _ cs L a ha β γ

end Plonk

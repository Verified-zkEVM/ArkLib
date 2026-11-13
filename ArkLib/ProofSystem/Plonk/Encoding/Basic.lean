/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Encoding.Domain
public import ArkLib.ProofSystem.Plonk.Relation.Prepared
public import Mathlib.LinearAlgebra.Lagrange

/-! # Polynomial encoding of Plonk

Interpolation identifies occurrence columns with polynomials of degree less than the domain size.
Prepared selectors and the public-input polynomial give a gate residual whose domain evaluations
are exactly the original row equations. The remaining relation is invariance under the wiring
permutation. All constructions are independent of an interaction framework.

The Mathlib polynomial model uses noncomputable finitely supported arithmetic and interpolation.
The executable refinement is provided in `Plonk.Computable`.
-/

@[expose] public section

namespace Plonk

open Polynomial

variable {F : Type} [Field F] {m n ℓ : ℕ}

namespace EvaluationDomain

/-- The unique interpolant of a column, using Mathlib's noncomputable polynomial arithmetic. -/
noncomputable def interpolate (D : EvaluationDomain F n) (v : Fin n → F) : degreeLT F n :=
  ⟨Lagrange.interpolate Finset.univ D.node v, mem_degreeLT.mpr (by
    simpa using Lagrange.degree_interpolate_lt (s := Finset.univ) v D.injective.injOn)⟩

@[simp]
theorem eval_interpolate (D : EvaluationDomain F n) (v : Fin n → F) (i : Fin n) :
    (D.interpolate v).val.eval (D.node i) = v i :=
  Lagrange.eval_interpolate_at_node v D.injective.injOn (Finset.mem_univ i)

/-- A polynomial of degree less than the domain size is determined by its node values. -/
theorem interpolate_unique (D : EvaluationDomain F n) (v : Fin n → F)
    (p : degreeLT F n) (hp : ∀ i, p.val.eval (D.node i) = v i) : p = D.interpolate v := by
  apply Subtype.ext
  exact Lagrange.eq_interpolate_of_eval_eq (s := Finset.univ) v D.injective.injOn
    (by simpa using mem_degreeLT.mp p.property) (fun i _ => hp i)

/-- Evaluation followed by interpolation recovers each degree-bounded polynomial. -/
@[simp]
theorem interpolate_eval (D : EvaluationDomain F n) (p : degreeLT F n) :
    D.interpolate (fun i => p.val.eval (D.node i)) = p :=
  (D.interpolate_unique _ p (fun _ => rfl)).symm

/-- Vanishing at every node of the evaluation domain. -/
def Vanishes (D : EvaluationDomain F n) (p : F[X]) : Prop :=
  ∀ i, p.eval (D.node i) = 0

/-- The indicator polynomial of a single row, using noncomputable interpolation. -/
noncomputable def lagrange (D : EvaluationDomain F n) (j : Fin n) : degreeLT F n :=
  D.interpolate (fun i => if i = j then 1 else 0)

@[simp]
theorem eval_lagrange (D : EvaluationDomain F n) (j i : Fin n) :
    (D.lagrange j).val.eval (D.node i) = if i = j then 1 else 0 :=
  D.eval_interpolate _ i

end EvaluationDomain

/-- Three degree-bounded witness columns, obtained by noncomputable interpolation. -/
noncomputable def wirePolynomials (D : EvaluationDomain F n) (w : Fin (3 * n) → F) :
    Fin 3 → degreeLT F n :=
  fun c => D.interpolate (fun i => w (finProdFinEquiv (c, i)))

/-- Evaluate polynomial columns at the position's row. -/
def polynomialOccurrences (D : EvaluationDomain F n) (a : Fin 3 → degreeLT F n)
    (p : Fin (3 * n)) : F :=
  (a (finProdFinEquiv.symm p).1).val.eval (D.node (finProdFinEquiv.symm p).2)

@[simp]
theorem polynomialOccurrences_column (D : EvaluationDomain F n) (a : Fin 3 → degreeLT F n)
    (c : Fin 3) (i : Fin n) :
    polynomialOccurrences D a (finProdFinEquiv (c, i)) = (a c).val.eval (D.node i) := by
  simp [polynomialOccurrences]

@[simp]
theorem eval_wirePolynomials (D : EvaluationDomain F n) (w : Fin (3 * n) → F)
    (c : Fin 3) (i : Fin n) :
    (wirePolynomials D w c).val.eval (D.node i) = w (finProdFinEquiv (c, i)) :=
  D.eval_interpolate _ i

@[simp]
theorem polynomialOccurrences_wirePolynomials (D : EvaluationDomain F n)
    (w : Fin (3 * n) → F) : polynomialOccurrences D (wirePolynomials D w) = w := by
  funext p
  obtain ⟨⟨c, i⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp

@[simp]
theorem wirePolynomials_polynomialOccurrences (D : EvaluationDomain F n)
    (a : Fin 3 → degreeLT F n) : wirePolynomials D (polynomialOccurrences D a) = a := by
  funext c
  simp [wirePolynomials]

/-- Occurrence columns and degree-bounded polynomial columns are equivalent.
The forward map uses noncomputable interpolation in the Mathlib model. -/
noncomputable def wirePolynomialEquiv (D : EvaluationDomain F n) :
    (Fin (3 * n) → F) ≃ (Fin 3 → degreeLT F n) where
  toFun := wirePolynomials D
  invFun := polynomialOccurrences D
  left_inv := polynomialOccurrences_wirePolynomials D
  right_inv := wirePolynomials_polynomialOccurrences D

/-- The five selector columns, using noncomputable interpolation. -/
noncomputable def selectorPolynomials (D : EvaluationDomain F n) (cs : ConstraintSystem F m n) :
    Selector (degreeLT F n) where
  qL := D.interpolate (fun i => (cs i).qL)
  qR := D.interpolate (fun i => (cs i).qR)
  qO := D.interpolate (fun i => (cs i).qO)
  qM := D.interpolate (fun i => (cs i).qM)
  qC := D.interpolate (fun i => (cs i).qC)

/-- The three columns of successor labels, using noncomputable interpolation. -/
noncomputable def permutationPolynomials (D : EvaluationDomain F n)
    (cs : ConstraintSystem F m n) (label : Fin (3 * n) → F) : Fin 3 → degreeLT F n :=
  fun c => D.interpolate (fun i => label (cs.perm (finProdFinEquiv (c, i))))

/-- Each permutation polynomial records the label of the permuted position. -/
@[simp]
theorem eval_permutationPolynomials (D : EvaluationDomain F n)
    (cs : ConstraintSystem F m n) (label : Fin (3 * n) → F) (c : Fin 3) (i : Fin n) :
    (permutationPolynomials D cs label c).val.eval (D.node i) =
      label (cs.perm (finProdFinEquiv (c, i))) := D.eval_interpolate _ i

/-- The public-input polynomial is negative input on reserved rows and zero elsewhere.
It uses Mathlib's noncomputable interpolation. -/
noncomputable def publicInputPolynomial (D : EvaluationDomain F n) (hrows : ℓ ≤ n)
    (x : Fin ℓ → F) : degreeLT F n :=
  D.interpolate (ConstraintSystem.publicInputTerm hrows x)

@[simp]
theorem eval_publicInputPolynomial (D : EvaluationDomain F n) (hrows : ℓ ≤ n)
    (x : Fin ℓ → F) (i : Fin n) :
    (publicInputPolynomial D hrows x).val.eval (D.node i) =
      ConstraintSystem.publicInputTerm hrows x i := D.eval_interpolate _ i

/-- The public-input polynomial is the negative sum of public values times row indicators. -/
theorem publicInputPolynomial_eq_sum (D : EvaluationDomain F n) (hrows : ℓ ≤ n) (x : Fin ℓ → F) :
    publicInputPolynomial D hrows x = -∑ j : Fin ℓ, x j • D.lagrange (Fin.castLE hrows j) := by
  symm
  apply D.interpolate_unique
  intro i
  simp only [Submodule.coe_neg, Submodule.coe_sum, Submodule.coe_smul,
    eval_neg, eval_finsetSum, eval_smul, EvaluationDomain.eval_lagrange]
  by_cases hi : i.val < ℓ
  · let j : Fin ℓ := ⟨i.val, hi⟩
    have hij : i = Fin.castLE hrows j := rfl
    have heq : ∀ k : Fin ℓ, i = Fin.castLE hrows k ↔ j = k := by
      intro k
      rw [hij, Fin.castLE_inj]
    simp [heq, ConstraintSystem.publicInputTerm, hi, j]
  · have hne : ∀ j : Fin ℓ, i ≠ Fin.castLE hrows j := by
      intro j hij
      apply hi
      rw [hij]
      exact j.isLt
    simp [ConstraintSystem.publicInputTerm, hi, hne]

/-- The gate residual, using Mathlib's noncomputable polynomial arithmetic. -/
noncomputable def gatePolynomial (q : Selector (degreeLT F n))
    (a : Fin 3 → degreeLT F n) (pi : degreeLT F n) : F[X] :=
  q.qL.val * (a 0).val + q.qR.val * (a 1).val + q.qO.val * (a 2).val +
    q.qM.val * ((a 0).val * (a 1).val) + q.qC.val + pi.val

/-- A gate residual built from degree-`< n` columns has degree at most `3(n - 1)`. -/
theorem degree_gatePolynomial_le (q : Selector (degreeLT F n))
    (a : Fin 3 → degreeLT F n) (pi : degreeLT F n) :
    (gatePolynomial q a pi).degree ≤ (3 * (n - 1) : ℕ) := by
  have h (p : degreeLT F n) : p.val.natDegree ≤ n - 1 := by
    by_cases hp : p.val = 0
    · simp [hp]
    · have hlt := (natDegree_lt_iff_degree_lt hp).mpr (mem_degreeLT.mp p.property)
      omega
  apply degree_le_of_natDegree_le
  unfold gatePolynomial
  repeat apply natDegree_add_le_of_degree_le
  · exact natDegree_mul_le.trans (by have := h q.qL; have := h (a 0); omega)
  · exact natDegree_mul_le.trans (by have := h q.qR; have := h (a 1); omega)
  · exact natDegree_mul_le.trans (by have := h q.qO; have := h (a 2); omega)
  · apply natDegree_mul_le.trans
    have hmul := natDegree_mul_le (p := (a 0).val) (q := (a 1).val)
    have := h q.qM
    have := h (a 0)
    have := h (a 1)
    omega
  · exact (h q.qC).trans (by omega)
  · exact (h pi).trans (by omega)

/-- Evaluating the gate polynomial gives the row residual and its public-input term. -/
theorem eval_gatePolynomial (D : EvaluationDomain F n) (cs : ConstraintSystem F m n)
    (a : Fin 3 → degreeLT F n) (pi : degreeLT F n) (i : Fin n) :
    (gatePolynomial (selectorPolynomials D cs) a pi).eval (D.node i) =
      cs.rowResidual (polynomialOccurrences D a) i + pi.val.eval (D.node i) := by
  simp [gatePolynomial, selectorPolynomials, ConstraintSystem.rowResidual]

/-- All gate equations hold exactly when the residual polynomial vanishes on the domain. -/
theorem gatePolynomial_vanishes_iff (D : EvaluationDomain F n) (cs : ConstraintSystem F m n)
    (a : Fin 3 → degreeLT F n) (pi : degreeLT F n) :
    D.Vanishes (gatePolynomial (selectorPolynomials D cs) a pi) ↔
      ∀ i, cs.rowResidual (polynomialOccurrences D a) i + pi.val.eval (D.node i) = 0 := by
  simp [EvaluationDomain.Vanishes, eval_gatePolynomial]

/-- Polynomial columns satisfy copies when their node values are invariant under wiring. -/
def SigmaConsistent (D : EvaluationDomain F n) (cs : ConstraintSystem F m n)
    (a : Fin 3 → degreeLT F n) : Prop :=
  ∀ p, polynomialOccurrences D a (cs.perm p) = polynomialOccurrences D a p

/-- Interpolation carries copy constraints exactly to sigma consistency. -/
theorem sigmaConsistent_iff (D : EvaluationDomain F n) (cs : ConstraintSystem F m n)
    (a : Fin 3 → degreeLT F n) :
    SigmaConsistent D cs a ↔ cs.CopyConstraintsSatisfied (polynomialOccurrences D a) :=
  (cs.copyConstraints_iff_invariant _).symm

/-- The prepared gate residual uses fixed selectors with cleared public constants.
Its mathematical polynomial arithmetic is noncomputable. -/
noncomputable def preparedGatePolynomial (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (a : Fin 3 → degreeLT F (ℓ + n)) : F[X] :=
  gatePolynomial (selectorPolynomials D (cs.prepare hℓ (fun _ => 0))) a
    (publicInputPolynomial D (Nat.le_add_right ℓ n) x)

/-- Clearing public constants and adding the public polynomial restores the original rows. -/
theorem eval_preparedGatePolynomial (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (a : Fin 3 → degreeLT F (ℓ + n)) (i : Fin (ℓ + n)) :
    (preparedGatePolynomial D cs hℓ x a).eval (D.node i) =
      (cs.prepare hℓ x).rowResidual (polynomialOccurrences D a) i := by
  rw [preparedGatePolynomial, eval_gatePolynomial, eval_publicInputPolynomial]
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [ConstraintSystem.rowResidual, ConstraintSystem.publicInputTerm, Gate.eq, j.isLt]
  · intro j
    simp [ConstraintSystem.rowResidual, ConstraintSystem.publicInputTerm]

/-- The polynomial relation consists of gate vanishing and sigma-consistent wire columns.
The circuit is prepared before the evaluation-domain size is chosen. -/
def PolynomialRelation (D : EvaluationDomain F (ℓ + n)) (cs : ConstraintSystem F m n)
    (hℓ : ℓ ≤ m) (x : Fin ℓ → F) (a : Fin 3 → degreeLT F (ℓ + n)) : Prop :=
  D.Vanishes (preparedGatePolynomial D cs hℓ x a) ∧ SigmaConsistent D (cs.prepare hℓ x) a

/-- The polynomial relation is exactly the prepared occurrence relation, including public inputs. -/
theorem polynomialRelation_iff_occurrenceRelation (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (a : Fin 3 → degreeLT F (ℓ + n)) :
    PolynomialRelation D cs hℓ x a ↔
      (cs.prepare hℓ x).occurrenceRelation (ConstraintSystem.preparedPublicOccurrence n) x
        (polynomialOccurrences D a) := by
  simp only [PolynomialRelation, EvaluationDomain.Vanishes, eval_preparedGatePolynomial,
    sigmaConsistent_iff, ConstraintSystem.occurrenceRelation]
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hc, hg, ?_⟩
    intro j
    have h := hg (j.castAdd n)
    simpa [ConstraintSystem.rowResidual, ConstraintSystem.preparedPublicOccurrence,
      Gate.eq, add_neg_eq_zero] using h
  · rintro ⟨hc, hg, _⟩
    exact ⟨hg, hc⟩

/-- Interpolation preserves and reflects the full prepared occurrence relation. -/
theorem polynomialRelation_wirePolynomials_iff (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (w : Fin (3 * (ℓ + n)) → F) :
    PolynomialRelation D cs hℓ x (wirePolynomials D w) ↔
      (cs.prepare hℓ x).occurrenceRelation (ConstraintSystem.preparedPublicOccurrence n) x w := by
  rw [polynomialRelation_iff_occurrenceRelation, polynomialOccurrences_wirePolynomials]

/-- Each original private witness satisfies exactly its interpolated polynomial relation. -/
theorem relation_iff_polynomialRelation (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (w : Fin (m - ℓ) → F) :
    relation cs ℓ hℓ x w ↔ PolynomialRelation D cs hℓ x
      (wirePolynomials D ((cs.prepare hℓ x).occurrences (fullAssignment hℓ x w))) := by
  rw [polynomialRelation_wirePolynomials_iff]
  constructor
  · intro hw
    apply (cs.prepare hℓ x).occurrences_relation (Fin.castLEEmb hℓ)
      (ConstraintSystem.preparedPublicOccurrence n) (cs.wireAt_preparedPublicOccurrence hℓ x)
    exact (relation_iff_variableRelation _ hℓ x w).mp ((cs.prepare_relation_iff hℓ x w).mpr hw)
  · intro hw
    apply (cs.prepare_relation_iff hℓ x w).mp
    change (cs.prepare hℓ x).accepts (fullAssignment hℓ x w)
    intro i
    change (cs.prepare hℓ x i).eval (fullAssignment hℓ x w) = 0
    rw [← ConstraintSystem.rowResidual_occurrences]
    exact hw.2.1 i

/-- Decode polynomial columns by their node values and the prepared occurrence decoder. -/
def decodePolynomials (D : EvaluationDomain F (ℓ + n)) (cs : ConstraintSystem F m n)
    (hℓ : ℓ ≤ m) (x : Fin ℓ → F) (a : Fin 3 → degreeLT F (ℓ + n)) : Fin (m - ℓ) → F :=
  cs.decodePrepared hℓ x (polynomialOccurrences D a)

/-- Every polynomial witness decodes to a private witness for the original circuit. -/
theorem relation_decodePolynomials (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (a : Fin 3 → degreeLT F (ℓ + n)) (ha : PolynomialRelation D cs hℓ x a) :
    relation cs ℓ hℓ x (decodePolynomials D cs hℓ x a) :=
  cs.relation_decodePrepared hℓ x _
    ((polynomialRelation_iff_occurrenceRelation D cs hℓ x a).mp ha)

/-- Re-encoding a decoded polynomial witness recovers every original wire polynomial. -/
theorem wirePolynomials_decodePolynomials (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (a : Fin 3 → degreeLT F (ℓ + n)) (ha : PolynomialRelation D cs hℓ x a) :
    wirePolynomials D ((cs.prepare hℓ x).occurrences
      (fullAssignment hℓ x (decodePolynomials D cs hℓ x a))) = a := by
  have hw := (polynomialRelation_iff_occurrenceRelation D cs hℓ x a).mp ha
  have hz := (cs.prepare hℓ x).assignmentOfOccurrences_relation (Fin.castLEEmb hℓ)
    (ConstraintSystem.preparedPublicOccurrence n) (cs.wireAt_preparedPublicOccurrence hℓ x)
    x (polynomialOccurrences D a) hw
  unfold decodePolynomials ConstraintSystem.decodePrepared
  rw [fullAssignment_privateWitness hℓ x _ hz.2,
    ConstraintSystem.occurrences_assignmentOfOccurrences _ _ hw.1,
    wirePolynomials_polynomialOccurrences]

/-- The original Plonk language equals the language of the polynomial relation. -/
theorem exists_relation_iff_exists_polynomialRelation (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F) :
    (∃ w, relation cs ℓ hℓ x w) ↔ ∃ a, PolynomialRelation D cs hℓ x a := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨_, (relation_iff_polynomialRelation D cs hℓ x w).mp hw⟩
  · rintro ⟨a, ha⟩
    exact ⟨decodePolynomials D cs hℓ x a, relation_decodePolynomials D cs hℓ x a ha⟩

end Plonk

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.GrandProduct.Data

/-! # Data and arithmetic for Plonk assembly

Executable polynomial tables decode to the private variables of the original circuit.
The grand-product, batching, and quotient error bounds add to `(7n - 3) / |F|`.
-/

@[expose] public section

open scoped NNReal

namespace Plonk.Assembly

/-- The three stage errors have numerator `7n - 3`. -/
theorem error_sum (n : ℕ) (hn : 2 ≤ n) (q : ℝ≥0) :
    ((3 * n - 1 : ℕ) : ℝ≥0) / q + 2 / q + ((4 * (n - 1) : ℕ) : ℝ≥0) / q =
      ((7 * n - 3 : ℕ) : ℝ≥0) / q := by
  have hnat : (3 * n - 1) + 2 + 4 * (n - 1) = 7 * n - 3 := by omega
  rw [← add_div, ← add_div]
  exact_mod_cast congrArg (fun a : ℕ => (a : ℝ≥0) / q) hnat

open CompPoly

variable {F : Type} [Field F] [DecidableEq F] {m n ℓ : ℕ}

/-- The public-input contribution encoded in executable coefficients. -/
def publicInputPolynomial (D : EvaluationDomain F (ℓ + n)) (hn : 0 < ℓ + n)
    (x : Fin ℓ → F) :
    GeneratorBatch.Poly F (ℓ + n) :=
  ⟨Computable.publicInputPolynomial D (Nat.le_add_right ℓ n) x, by
    rw [Computable.publicInputPolynomial_toPoly]
    have h := (Plonk.publicInputPolynomial D (Nat.le_add_right ℓ n) x).property
    by_cases hz : (Plonk.publicInputPolynomial D (Nat.le_add_right ℓ n) x).val = 0
    · simpa [hz] using hn
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (Polynomial.mem_degreeLT.mp h)⟩

/-- Executable public-input coefficients represent the mathematical public polynomial. -/
@[simp]
theorem publicInputPolynomial_toPoly (D : EvaluationDomain F (ℓ + n))
    (hn : 0 < ℓ + n) (x : Fin ℓ → F) :
    (publicInputPolynomial D hn x).val.toPoly =
      (Plonk.publicInputPolynomial D (Nat.le_add_right ℓ n) x).val := by
  simp [publicInputPolynomial]

/-- Evaluate an executable table at each wire position. -/
def occurrences (D : EvaluationDomain F n) (a : Fin 3 → GeneratorBatch.Poly F n)
    (p : Fin (3 * n)) : F :=
  CPolynomial.evalHorner (D.node (finProdFinEquiv.symm p).2)
    (a (finProdFinEquiv.symm p).1).val

/-- Executable row evaluation agrees with the polynomial interpretation. -/
theorem occurrences_eq (D : EvaluationDomain F n) (a : Fin 3 → GeneratorBatch.Poly F n) :
    occurrences D a = polynomialOccurrences D (GrandProduct.wires a) := by
  funext p
  simp [occurrences, polynomialOccurrences, GrandProduct.wires, GrandProduct.mathPoly,
    CPolynomial.eval_horner_eq_eval, CPolynomial.eval_toPoly]

/-- Decode the revealed initial polynomial table into the original private witness. -/
def circuitExtractor (D : EvaluationDomain F (ℓ + n)) (cs : ConstraintSystem F m n)
    (hℓ : ℓ ≤ m) (x : Fin ℓ → F) (a : Fin 3 → GeneratorBatch.Poly F (ℓ + n)) :
    Fin (m - ℓ) → F :=
  cs.decodePrepared hℓ x (occurrences D a)

omit [DecidableEq F] in
/-- Changing the prepared public constants leaves every wire index unchanged. -/
theorem prepared_wireAt_eq (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m)
    (x y : Fin ℓ → F) : (cs.prepare hℓ x).wireAt = (cs.prepare hℓ y).wireAt := by
  funext p
  obtain ⟨⟨c, i⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp only [ConstraintSystem.wireAt, Equiv.symm_apply_apply]
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [Gate.eq]
  · intro j
    simp

/-- Grand-product input validity is the prepared polynomial relation. -/
theorem inputRelation_iff_polynomialRelation (ω : F)
    (hω : IsPrimitiveRoot ω (ℓ + n)) (hn : 0 < ℓ + n)
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (a : Fin 3 → GeneratorBatch.Poly F (ℓ + n)) :
    GrandProduct.InputRelation ω hω (cs.prepare hℓ (fun _ => 0))
      (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) hn x) a ↔
    PolynomialRelation (EvaluationDomain.primitiveRoot ω hω) cs hℓ x (GrandProduct.wires a) := by
  have hpi : GrandProduct.mathPoly
      (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) hn x) =
      Plonk.publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω)
        (Nat.le_add_right ℓ n) x := by
    apply Subtype.ext
    exact publicInputPolynomial_toPoly _ _ _
  simp only [GrandProduct.InputRelation, GrandProduct.gate_toPoly, hpi,
    PolynomialRelation, preparedGatePolynomial, sigmaConsistent_iff,
    ConstraintSystem.CopyConstraintsSatisfied, prepared_wireAt_eq cs hℓ (fun _ => 0) x]

/-- A valid initial polynomial table decodes to a witness of the original circuit. -/
theorem relation_circuitExtractor (ω : F) (hω : IsPrimitiveRoot ω (ℓ + n))
    (hn : 0 < ℓ + n) (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (a : Fin 3 → GeneratorBatch.Poly F (ℓ + n))
    (ha : GrandProduct.InputRelation ω hω (cs.prepare hℓ (fun _ => 0))
      (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) hn x) a) :
    relation cs ℓ hℓ x
      (circuitExtractor (EvaluationDomain.primitiveRoot ω hω) cs hℓ x a) := by
  unfold circuitExtractor
  rw [occurrences_eq]
  exact relation_decodePolynomials _ cs hℓ x (GrandProduct.wires a)
    ((inputRelation_iff_polynomialRelation ω hω hn cs hℓ x a).mp ha)

/-- Interpolate the three wire columns of the original circuit witness. -/
def honestWires (D : EvaluationDomain F (ℓ + n)) (hn : 0 < ℓ + n)
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (w : Fin (m - ℓ) → F) : Fin 3 → GeneratorBatch.Poly F (ℓ + n) :=
  fun c => ⟨Computable.wirePolynomials D
      ((cs.prepare hℓ x).occurrences (fullAssignment hℓ x w)) c, by
    rw [Computable.wirePolynomials_toPoly]
    have h := (wirePolynomials D
      ((cs.prepare hℓ x).occurrences (fullAssignment hℓ x w)) c).property
    by_cases hz : (wirePolynomials D
        ((cs.prepare hℓ x).occurrences (fullAssignment hℓ x w)) c).val = 0
    · simpa [hz] using hn
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr
        (Polynomial.mem_degreeLT.mp h)⟩

/-- Honest executable wire columns represent the interpolated satisfying assignment. -/
@[simp]
theorem wires_honestWires (D : EvaluationDomain F (ℓ + n)) (hn : 0 < ℓ + n)
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (w : Fin (m - ℓ) → F) :
    GrandProduct.wires (honestWires D hn cs hℓ x w) =
      wirePolynomials D ((cs.prepare hℓ x).occurrences (fullAssignment hℓ x w)) := by
  funext c
  apply Subtype.ext
  simp [GrandProduct.wires, GrandProduct.mathPoly, honestWires]

/-- Every satisfying circuit witness supplies a valid initial polynomial table. -/
theorem inputRelation_honestWires (ω : F) (hω : IsPrimitiveRoot ω (ℓ + n))
    (hn : 0 < ℓ + n) (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (w : Fin (m - ℓ) → F) (hw : relation cs ℓ hℓ x w) :
    GrandProduct.InputRelation ω hω (cs.prepare hℓ (fun _ => 0))
      (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) hn x)
      (honestWires (EvaluationDomain.primitiveRoot ω hω) hn cs hℓ x w) := by
  rw [inputRelation_iff_polynomialRelation, wires_honestWires]
  exact (relation_iff_polynomialRelation _ cs hℓ x w).mp hw

end Plonk.Assembly

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.GeneratorBatch
public import ArkLib.ProofSystem.Plonk.Accumulator.Computable

/-! # Plonk permutation grand product: degree-bounded data

Executable wire polynomials and the univariate accumulator over the multiplicative evaluation
domain determine the three Plonk residuals. They encode `Z(1) = 1` and
`Z(ωx) * Q(x) = Z(x) * N(x)` for checking through the quotient zero test. Their mathematical
interpretations support completeness outside the explicit zero-factor bad set and the
division-free reduction from residual vanishing to the permutation fingerprint.
-/

@[expose] public section

namespace Plonk.GrandProduct

open Polynomial CompPoly

variable {F : Type} [Field F] [DecidableEq F] {m n : ℕ}

/-- The mathematical view of an executable polynomial. Mathlib's polynomial representation is
noncomputable; the underlying coefficient array remains executable. -/
noncomputable def mathPoly (p : GeneratorBatch.Poly F n) : degreeLT F n :=
  ⟨p.val.toPoly, mem_degreeLT.mpr (degree_le_natDegree.trans_lt (by exact_mod_cast p.property))⟩

/-- The mathematical view of the three wire columns. -/
noncomputable def wires (a : Fin 3 → GeneratorBatch.Poly F n) : Fin 3 → degreeLT F n :=
  fun c => mathPoly (a c)

/-- The common residual degree budget. -/
def residualDegree (n : ℕ) : ℕ := 4 * (n - 1)

variable (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 2 ≤ n)
  (cs : ConstraintSystem F m n)
  (L : CosetLabels (EvaluationDomain.primitiveRoot ω hω))

/-- Compute the numerator from the retained wire polynomials. -/
def numerator (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) : CPolynomial F :=
  Computable.accumulatorNumerator (fun c => (a c).val) L.multiplier β γ

/-- Compute the denominator from retained wires and the fixed permutation columns. -/
def denominator (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) : CPolynomial F :=
  Computable.accumulatorDenominator (fun c => (a c).val)
    (Computable.permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ

/-- The executable numerator represents the labeled mathematical product. -/
@[simp]
theorem numerator_toPoly (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) :
    (numerator ω hω L a β γ).toPoly = accumulatorNumerator (wires a) L.multiplier β γ :=
  Computable.accumulatorNumerator_toPoly _ _ (fun _ => rfl) _ _ _

/-- The executable denominator represents the permuted mathematical product. -/
@[simp]
theorem denominator_toPoly (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) :
    (denominator ω hω cs L a β γ).toPoly = accumulatorDenominator (wires a)
      (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ :=
  Computable.accumulatorDenominator_toPoly _ _ _ _ (fun _ => rfl)
    (fun c => Computable.permutationPolynomials_toPoly _ _ _ c) _ _

/-- Compute the gate residual within the common degree budget. -/
def gate (pi : GeneratorBatch.Poly F n) (a : Fin 3 → GeneratorBatch.Poly F n) :
    GeneratorBatch.Poly F (residualDegree n + 1) :=
  ⟨Computable.gatePolynomial
    (Computable.selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs)
    (fun c => (a c).val) pi.val, by
    have heq : (Computable.gatePolynomial
        (Computable.selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs)
        (fun c => (a c).val) pi.val).toPoly =
        gatePolynomial (selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs)
          (wires a) (mathPoly pi) := by
      simp [Computable.gatePolynomial, gatePolynomial, Computable.selectorPolynomials,
        selectorPolynomials, wires, mathPoly]
    rw [heq]
    have h := natDegree_le_of_degree_le (degree_gatePolynomial_le
      (selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs) (wires a) (mathPoly pi))
    dsimp [residualDegree]
    omega⟩

/-- The executable gate residual represents the usual gate equation. -/
@[simp]
theorem gate_toPoly (pi : GeneratorBatch.Poly F n) (a : Fin 3 → GeneratorBatch.Poly F n) :
    (gate ω hω cs pi a).val.toPoly =
      gatePolynomial (selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs)
        (wires a) (mathPoly pi) := by
  simp [gate, Computable.gatePolynomial, gatePolynomial, Computable.selectorPolynomials,
    selectorPolynomials, wires, mathPoly]

/-- Compute the recurrence residual within the common degree budget. -/
def recurrence (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) (Z : GeneratorBatch.Poly F n) :
    GeneratorBatch.Poly F (residualDegree n + 1) :=
  ⟨Computable.recurrenceResidual ω (numerator ω hω L a β γ)
    (denominator ω hω cs L a β γ) Z.val, by
    rw [Computable.recurrenceResidual_toPoly, numerator_toPoly, denominator_toPoly]
    exact Nat.lt_succ_of_le (natDegree_le_of_degree_le
      (degree_accumulatorRecurrenceResidual_le hn (wires a)
        (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label)
        L.multiplier β γ ω (mathPoly Z)))⟩

/-- The executable recurrence residual represents the multiplication-form recurrence. -/
@[simp]
theorem recurrence_toPoly (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F)
    (Z : GeneratorBatch.Poly F n) :
    (recurrence ω hω hn cs L a β γ Z).val.toPoly =
      recurrenceResidual ω (accumulatorNumerator (wires a) L.multiplier β γ)
        (accumulatorDenominator (wires a)
          (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ)
        Z.val.toPoly := by
  simp [recurrence]

/-- Compute the first-row normalization residual within the common degree budget. -/
def boundary (Z : GeneratorBatch.Poly F n) : GeneratorBatch.Poly F (residualDegree n + 1) :=
  ⟨Computable.boundaryResidual (EvaluationDomain.primitiveRoot ω hω) (by omega) Z.val, by
    rw [Computable.boundaryResidual_toPoly]
    have h := natDegree_le_of_degree_le
      (degree_boundaryResidual_le (EvaluationDomain.primitiveRoot ω hω) (by omega) (mathPoly Z))
    dsimp [mathPoly] at h
    dsimp [residualDegree]
    omega⟩

/-- The executable boundary residual represents first-row normalization. -/
@[simp]
theorem boundary_toPoly (Z : GeneratorBatch.Poly F n) :
    (boundary ω hω hn Z).val.toPoly =
      boundaryResidual (EvaluationDomain.primitiveRoot ω hω) (by omega) Z.val.toPoly := by
  simp [boundary]

/-- A gate query uses only the three wire evaluations and fixed public polynomials. -/
theorem eval_gate (pi : GeneratorBatch.Poly F n) (a : Fin 3 → GeneratorBatch.Poly F n) (x : F) :
    CPolynomial.evalHorner x (gate ω hω cs pi a).val =
      CPolynomial.evalHorner x
          (Computable.selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs).qL *
        CPolynomial.evalHorner x (a 0).val +
      CPolynomial.evalHorner x
          (Computable.selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs).qR *
        CPolynomial.evalHorner x (a 1).val +
      CPolynomial.evalHorner x
          (Computable.selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs).qO *
        CPolynomial.evalHorner x (a 2).val +
      CPolynomial.evalHorner x
          (Computable.selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs).qM *
        (CPolynomial.evalHorner x (a 0).val * CPolynomial.evalHorner x (a 1).val) +
      CPolynomial.evalHorner x
          (Computable.selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs).qC +
      CPolynomial.evalHorner x pi.val := by
  simp [CPolynomial.eval_horner_eq_eval, CPolynomial.eval_toPoly, gate,
    Computable.gatePolynomial]

/-- A numerator query multiplies the three affine wire evaluations. -/
theorem eval_numerator (a : Fin 3 → GeneratorBatch.Poly F n) (β γ x : F) :
    CPolynomial.evalHorner x (numerator ω hω L a β γ) =
      ∏ c, (CPolynomial.evalHorner x (a c).val + β * L.multiplier c * x + γ) := by
  simp [CPolynomial.eval_horner_eq_eval, CPolynomial.eval_toPoly, wires, mathPoly]

/-- A denominator query uses the fixed permutation evaluations. -/
theorem eval_denominator (a : Fin 3 → GeneratorBatch.Poly F n) (β γ x : F) :
    CPolynomial.evalHorner x (denominator ω hω cs L a β γ) =
      ∏ c, (CPolynomial.evalHorner x (a c).val + β *
        CPolynomial.evalHorner x
          (Computable.permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label c)
        + γ) := by
  simp [CPolynomial.eval_horner_eq_eval, CPolynomial.eval_toPoly, wires, mathPoly]

/-- A recurrence query needs accumulator evaluations at `x` and `ωx`. -/
theorem eval_recurrence (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F)
    (Z : GeneratorBatch.Poly F n) (x : F) :
    CPolynomial.evalHorner x (recurrence ω hω hn cs L a β γ Z).val =
      CPolynomial.evalHorner (ω * x) Z.val *
        CPolynomial.evalHorner x (denominator ω hω cs L a β γ) -
      CPolynomial.evalHorner x Z.val *
        CPolynomial.evalHorner x (numerator ω hω L a β γ) := by
  simp [CPolynomial.eval_horner_eq_eval, CPolynomial.eval_toPoly]

/-- A boundary query uses the first-row indicator and one accumulator evaluation. -/
theorem eval_boundary (Z : GeneratorBatch.Poly F n) (x : F) :
    CPolynomial.evalHorner x (boundary ω hω hn Z).val =
      CPolynomial.evalHorner x (Computable.interpolate (EvaluationDomain.primitiveRoot ω hω)
        (fun i => if i = ⟨0, by omega⟩ then 1 else 0)) *
      (CPolynomial.evalHorner x Z.val - 1) := by
  simp [CPolynomial.eval_horner_eq_eval, CPolynomial.eval_toPoly, boundary,
    Computable.boundaryResidual]

/-- Gate, recurrence and boundary residuals, in that order. -/
def residuals (pi : GeneratorBatch.Poly F n) (a : Fin 3 → GeneratorBatch.Poly F n)
    (β γ : F) (Z : GeneratorBatch.Poly F n) :
    Fin 3 → GeneratorBatch.Poly F (residualDegree n + 1) :=
  ![gate ω hω cs pi a, recurrence ω hω hn cs L a β γ Z, boundary ω hω hn Z]

/-- Compute the honest normalized accumulator by interpolating ratio prefixes. -/
def honestAccumulator (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) :
    GeneratorBatch.Poly F n :=
  ⟨Computable.honestAccumulator ω hω (numerator ω hω L a β γ)
      (denominator ω hω cs L a β γ), by
    rw [Computable.honestAccumulator_toPoly, numerator_toPoly, denominator_toPoly]
    have h := mem_degreeLT.mp (Plonk.honestAccumulator ω hω
      (accumulatorNumerator (wires a) L.multiplier β γ)
      (accumulatorDenominator (wires a)
        (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ)).property
    by_cases hz : (Plonk.honestAccumulator ω hω
      (accumulatorNumerator (wires a) L.multiplier β γ)
      (accumulatorDenominator (wires a)
        (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ)).val = 0
    · simp [hz]; omega
    · exact (natDegree_lt_iff_degree_lt hz).mpr h⟩

/-- Honest coefficient-array interpolation agrees with the mathematical accumulator. -/
@[simp]
theorem honestAccumulator_toPoly (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) :
    (honestAccumulator ω hω hn cs L a β γ).val.toPoly =
      (Plonk.honestAccumulator ω hω (accumulatorNumerator (wires a) L.multiplier β γ)
        (accumulatorDenominator (wires a)
          (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ)).val := by
  simp [honestAccumulator]

/-- Valid initial wire columns satisfy the gate and copy constraints. -/
def InputRelation (pi : GeneratorBatch.Poly F n) (a : Fin 3 → GeneratorBatch.Poly F n) : Prop :=
  (EvaluationDomain.primitiveRoot ω hω).Vanishes (gate ω hω cs pi a).val.toPoly ∧
    cs.CopyConstraintsSatisfied
      (polynomialOccurrences (EvaluationDomain.primitiveRoot ω hω) (wires a))

/-- The output claim is vanishing of all three residuals on the row domain. -/
def OutputRelation (pi : GeneratorBatch.Poly F n) (a : Fin 3 → GeneratorBatch.Poly F n)
    (β γ : F) (Z : GeneratorBatch.Poly F n) : Prop :=
  ∀ j, (EvaluationDomain.primitiveRoot ω hω).Vanishes
    (residuals ω hω hn cs L pi a β γ Z j).val.toPoly

/-- The explicit bad challenge set consists of zero denominator factors. -/
def BadChallenge (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) : Prop :=
  Plonk.BadChallenge (EvaluationDomain.primitiveRoot ω hω) (wires a)
    (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ

/-- All residuals vanish precisely when gates vanish and the accumulator is normalized and
satisfies the division-free recurrence. -/
theorem outputRelation_iff (pi : GeneratorBatch.Poly F n) (a : Fin 3 → GeneratorBatch.Poly F n)
    (β γ : F) (Z : GeneratorBatch.Poly F n) :
    OutputRelation ω hω hn cs L pi a β γ Z ↔
      (EvaluationDomain.primitiveRoot ω hω).Vanishes (gate ω hω cs pi a).val.toPoly ∧
      AccumulatorRelation (EvaluationDomain.primitiveRoot ω hω) ω
        (accumulatorNumerator (wires a) L.multiplier β γ)
        (accumulatorDenominator (wires a)
          (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label) β γ)
        Z.val.toPoly := by
  rw [accumulatorRelation_iff_vanishes ω hω (by omega)]
  simp only [OutputRelation, residuals, Fin.forall_fin_succ, Fin.isValue,
    Matrix.cons_val_zero, gate_toPoly, Matrix.cons_val_succ,
    recurrence_toPoly, boundary_toPoly, Fin.forall_fin_zero, and_true]
  tauto

/-- Valid input columns yield vanishing honest residuals outside the explicit bad set. -/
theorem honest_outputRelation (pi : GeneratorBatch.Poly F n) (a : Fin 3 → GeneratorBatch.Poly F n)
    (ha : InputRelation ω hω cs pi a) (β γ : F)
    (hgood : ¬ BadChallenge ω hω cs L a β γ) :
    OutputRelation ω hω hn cs L pi a β γ (honestAccumulator ω hω hn cs L a β γ) := by
  apply (outputRelation_iff ω hω hn cs L pi a β γ _).mpr
  refine ⟨ha.1, ?_⟩
  rw [honestAccumulator_toPoly]
  exact honestAccumulator_relation_of_copy ω hω (by omega) cs L (wires a) β γ ha.2 hgood

/-- Vanishing residuals force the fingerprint to vanish, including at zero factors. -/
theorem fingerprint_eq_zero_of_output (pi : GeneratorBatch.Poly F n)
    (a : Fin 3 → GeneratorBatch.Poly F n) (β γ : F) (Z : GeneratorBatch.Poly F n)
    (h : OutputRelation ω hω hn cs L pi a β γ Z) :
    PermutationFingerprint.fingerprint
      (polynomialOccurrences (EvaluationDomain.primitiveRoot ω hω) (wires a))
      L.labelEmbedding cs.perm β γ = 0 :=
  fingerprint_eq_zero_of_accumulator ω hω cs L (wires a) β γ Z.val.toPoly
    ((outputRelation_iff ω hω hn cs L pi a β γ Z).mp h).2

end Plonk.GrandProduct

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Encoding.Basic
public import CompPoly.Univariate.Lagrange

/-! # Executable Plonk polynomial encoding

Coefficient-array interpolation computes the fixed selector and permutation polynomials, wire
polynomials, and public-input contribution. Its interpretation agrees with the degree-bounded
Mathlib encoding.
-/

@[expose] public section

namespace Plonk.Computable

open CompPoly

variable {F : Type} [Field F] [BEq F] [LawfulBEq F] {m n ℓ : ℕ}

/-- Interpolate a row column using executable coefficient arrays. -/
def interpolate (D : EvaluationDomain F n) (v : Fin n → F) : CPolynomial F :=
  CPolynomial.CLagrange.interpolate Finset.univ D.node v

/-- Coefficient-array interpolation represents the degree-bounded mathematical interpolant. -/
@[simp]
theorem interpolate_toPoly (D : EvaluationDomain F n) (v : Fin n → F) :
    (interpolate D v).toPoly = (D.interpolate v).val := by
  exact CPolynomial.CLagrange.cinterpolate_eq_interpolate

/-- The executable interpolant has degree less than the number of rows. -/
theorem interpolate_mem_degreeLT (D : EvaluationDomain F n) (v : Fin n → F) :
    interpolate D v ∈ CPolynomial.degreeLT (R := F) n := by
  rw [CPolynomial.degreeLT_toPoly, interpolate_toPoly]
  exact (D.interpolate v).property

/-- The executable interpolant takes the supplied value at every row. -/
@[simp]
theorem eval_interpolate (D : EvaluationDomain F n) (v : Fin n → F) (i : Fin n) :
    (interpolate D v).eval (D.node i) = v i := by
  rw [CPolynomial.eval_toPoly, interpolate_toPoly, D.eval_interpolate]

/-- Encode the five fixed selector columns. -/
def selectorPolynomials (D : EvaluationDomain F n) (cs : ConstraintSystem F m n) :
    Selector (CPolynomial F) where
  qL := interpolate D (fun i => (cs i).qL)
  qR := interpolate D (fun i => (cs i).qR)
  qO := interpolate D (fun i => (cs i).qO)
  qM := interpolate D (fun i => (cs i).qM)
  qC := interpolate D (fun i => (cs i).qC)

/-- Encode the three occurrence columns. -/
def wirePolynomials (D : EvaluationDomain F n) (w : Fin (3 * n) → F) :
    Fin 3 → CPolynomial F :=
  fun c => interpolate D (fun i => w (finProdFinEquiv (c, i)))

/-- Encode the position labels reached by the wiring permutation. -/
def permutationPolynomials (D : EvaluationDomain F n) (cs : ConstraintSystem F m n)
    (label : Fin (3 * n) → F) : Fin 3 → CPolynomial F :=
  fun c => interpolate D (fun i => label (cs.perm (finProdFinEquiv (c, i))))

/-- Encode the public-input contribution on the reserved rows. -/
def publicInputPolynomial (D : EvaluationDomain F n) (hrows : ℓ ≤ n) (x : Fin ℓ → F) :
    CPolynomial F :=
  interpolate D (ConstraintSystem.publicInputTerm hrows x)

/-- Assemble the gate residual from executable polynomials. -/
def gatePolynomial (q : Selector (CPolynomial F)) (a : Fin 3 → CPolynomial F)
    (pi : CPolynomial F) : CPolynomial F :=
  q.qL * a 0 + q.qR * a 1 + q.qO * a 2 + q.qM * (a 0 * a 1) + q.qC + pi

/-- Each executable selector represents its mathematical selector. -/
theorem selectorPolynomials_toPoly (D : EvaluationDomain F n)
    (cs : ConstraintSystem F m n) :
    (selectorPolynomials D cs).qL.toPoly = (Plonk.selectorPolynomials D cs).qL.val ∧
    (selectorPolynomials D cs).qR.toPoly = (Plonk.selectorPolynomials D cs).qR.val ∧
    (selectorPolynomials D cs).qO.toPoly = (Plonk.selectorPolynomials D cs).qO.val ∧
    (selectorPolynomials D cs).qM.toPoly = (Plonk.selectorPolynomials D cs).qM.val ∧
    (selectorPolynomials D cs).qC.toPoly = (Plonk.selectorPolynomials D cs).qC.val := by
  simp only [selectorPolynomials, Plonk.selectorPolynomials, interpolate_toPoly, and_self]

/-- Executable wire encoding agrees with the mathematical wire encoding. -/
@[simp]
theorem wirePolynomials_toPoly (D : EvaluationDomain F n) (w : Fin (3 * n) → F)
    (c : Fin 3) :
    (wirePolynomials D w c).toPoly = (Plonk.wirePolynomials D w c).val := by
  exact interpolate_toPoly D _

/-- Executable permutation encoding agrees with the mathematical permutation encoding. -/
@[simp]
theorem permutationPolynomials_toPoly (D : EvaluationDomain F n)
    (cs : ConstraintSystem F m n) (label : Fin (3 * n) → F) (c : Fin 3) :
    (permutationPolynomials D cs label c).toPoly =
      (Plonk.permutationPolynomials D cs label c).val := by
  exact interpolate_toPoly D _

/-- Executable public-input encoding agrees with the mathematical public-input encoding. -/
@[simp]
theorem publicInputPolynomial_toPoly (D : EvaluationDomain F n)
    (hrows : ℓ ≤ n) (x : Fin ℓ → F) :
    (publicInputPolynomial D hrows x).toPoly =
      (Plonk.publicInputPolynomial D hrows x).val := by
  exact interpolate_toPoly D _

/-- The executable gate residual represents the mathematical residual exactly. -/
theorem gatePolynomial_toPoly (D : EvaluationDomain F n) (cs : ConstraintSystem F m n)
    (w : Fin (3 * n) → F) (hrows : ℓ ≤ n) (x : Fin ℓ → F) :
    (gatePolynomial (selectorPolynomials D cs) (wirePolynomials D w)
      (publicInputPolynomial D hrows x)).toPoly =
      Plonk.gatePolynomial (Plonk.selectorPolynomials D cs) (Plonk.wirePolynomials D w)
        (Plonk.publicInputPolynomial D hrows x) := by
  simp only [gatePolynomial, Plonk.gatePolynomial, CPolynomial.toPoly_add,
    CPolynomial.toPoly_mul, wirePolynomials_toPoly, publicInputPolynomial_toPoly,
    selectorPolynomials, Plonk.selectorPolynomials, interpolate_toPoly]

/-- The executable prepared residual uses cleared fixed selectors and the public input once. -/
def preparedGatePolynomial (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (w : Fin (3 * (ℓ + n)) → F) : CPolynomial F :=
  gatePolynomial (selectorPolynomials D (cs.prepare hℓ (fun _ => 0)))
    (wirePolynomials D w) (publicInputPolynomial D (Nat.le_add_right ℓ n) x)

/-- Executable prepared residuals agree with the mathematical prepared residuals. -/
theorem preparedGatePolynomial_toPoly (D : EvaluationDomain F (ℓ + n))
    (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
    (w : Fin (3 * (ℓ + n)) → F) :
    (preparedGatePolynomial D cs hℓ x w).toPoly =
      Plonk.preparedGatePolynomial D cs hℓ x (Plonk.wirePolynomials D w) :=
  gatePolynomial_toPoly D _ w _ x

end Plonk.Computable

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Terminal

/-!
# Query realizations of Spartan's virtual polynomials

The first virtual polynomial is evaluated by contracting each matrix row slice against the
assignment over Boolean column points. These computations query only the retained matrix and
witness oracles.
-/

@[expose] public section

namespace Spartan.VirtualOracle

open OracleComp OracleInterface ProtocolSpec Realization MvPolynomial

variable {R : Type} [CommRing R] (pp : PublicParams)

local instance : ∀ i, OracleInterface (OracleStatement (R := R) pp i) :=
  Terminal.oracleInterface pp

/-- One Boolean-column term in a matrix-vector contraction. -/
def columnTerm (x : R1CS.Statement R pp.toSizeR1CS)
    (r_x : Fin pp.ℓ_m → R) (i : R1CS.MatrixIdx) (b : Fin pp.ℓ_n → Fin 2) :
    OracleComp [OracleStatement (R := R) pp]ₒ R := do
  let r_y : Fin pp.ℓ_n → R := fun j => (b j : R)
  let value : R ← query (spec := [OracleStatement (R := R) pp]ₒ) ⟨.inl i, (r_x, r_y)⟩
  let w ← query (spec := [OracleStatement (R := R) pp]ₒ) ⟨.inr 0, witnessPoint pp r_y⟩
  return value * assignmentEval pp x r_y w

/-- A row-product evaluation obtained by oracle queries over all Boolean columns. -/
def row (x : R1CS.Statement R pp.toSizeR1CS)
    (r_x : Fin pp.ℓ_m → R) (i : R1CS.MatrixIdx) :
    OracleComp [OracleStatement (R := R) pp]ₒ R := do
  let values ← (List.ofFn (fun j : Fin (2 ^ pp.ℓ_n) => j)).mapM fun j =>
    columnTerm pp x r_x i (finFunctionFinEquiv.symm j)
  return values.sum

/-- Evaluate the first virtual polynomial through the retained oracle interfaces. -/
def first (x : R1CS.Statement R pp.toSizeR1CS) (τ r_x : Fin pp.ℓ_m → R) :
    OracleComp [OracleStatement (R := R) pp]ₒ R := do
  let a ← row pp x r_x .A
  let b ← row pp x r_x .B
  let c ← row pp x r_x .C
  return eqWeight τ r_x * (a * b - c)

/-- A column query returns precisely the corresponding semantic contraction term. -/
theorem columnTerm_realizes (x : R1CS.Statement R pp.toSizeR1CS)
    (r_x : Fin pp.ℓ_m → R) (i : R1CS.MatrixIdx) (b : Fin pp.ℓ_n → Fin 2)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    simulateQ (simOracle0 (OracleStatement (R := R) pp) o) (columnTerm pp x r_x i b) =
      pure (eval (b : Fin pp.ℓ_n → R) (eval (C ∘ r_x) (o (.inl i)).toMLE) *
        eval (b : Fin pp.ℓ_n → R) (MLE' (R1CS.𝕫 x (o (.inr 0))))) := by
  change pure (matrixEval (o (.inl i)) r_x (b : Fin pp.ℓ_n → R) *
    assignmentEval pp x (b : Fin pp.ℓ_n → R)
      (tableEval (o (.inr 0)) (witnessPoint pp (b : Fin pp.ℓ_n → R)))) =
    (pure _ : Id R)
  congr 1
  exact congrArg₂ (· * ·)
    (matrixEval_eq (m := pp.ℓ_m) (n := pp.ℓ_n) (o (.inl i)) r_x _)
    (assignmentEval_realizes pp x (o (.inr 0)) _)

/-- Query contraction realizes the row-product polynomial. -/
theorem row_realizes (x : R1CS.Statement R pp.toSizeR1CS)
    (r_x : Fin pp.ℓ_m → R) (i : R1CS.MatrixIdx)
    (o : ∀ i, OracleStatement (R := R) pp i) :
    simulateQ (simOracle0 (OracleStatement (R := R) pp) o) (row pp x r_x i) =
      pure (eval r_x (Algebra.rowProduct (o (.inl i)) (R1CS.𝕫 x (o (.inr 0))))) := by
  simp only [row, simulateQ_bind, simulateQ_list_mapM, columnTerm_realizes, List.mapM_pure,
    pure_bind, List.map_ofFn, List.sum_ofFn, simulateQ_pure]
  congr 1
  apply Eq.trans ?_ (Algebra.rowProduct_eval_eq_contraction
    (m := pp.ℓ_m) (n := pp.ℓ_n) (o (.inl i)) (R1CS.𝕫 x (o (.inr 0))) r_x).symm
  exact Equiv.sum_comp finFunctionFinEquiv.symm
    (fun b : Fin pp.ℓ_n → Fin 2 =>
      eval (b : Fin pp.ℓ_n → R) (eval (C ∘ r_x) (o (.inl i)).toMLE) *
        eval (b : Fin pp.ℓ_n → R) (MLE' (R1CS.𝕫 x (o (.inr 0)))))

/-- The oracle-query implementation realizes the semantic first virtual polynomial. -/
theorem firstVirtual_realizes (x : R1CS.Statement R pp.toSizeR1CS)
    (τ r_x : Fin pp.ℓ_m → R) (o : ∀ i, OracleStatement (R := R) pp i) :
    simulateQ (simOracle0 (OracleStatement (R := R) pp) o) (first pp x τ r_x) =
      pure (eval r_x (Algebra.firstVirtual (fun i => o (.inl i))
        (R1CS.𝕫 x (o (.inr 0))) τ)) := by
  simp only [first, simulateQ_bind, row_realizes, pure_bind, simulateQ_pure,
    eqWeight_eq]
  congr 1
  exact (Algebra.firstVirtual_eval (m := pp.ℓ_m) (n := pp.ℓ_n)
    (fun i => o (.inl i)) (R1CS.𝕫 x (o (.inr 0))) τ r_x).symm

end Spartan.VirtualOracle

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Spartan.Algebra.Realization

/-!
# Spartan's initial zero-check relation

Satisfaction of the retained R1CS witness is equivalent to the residual interpolation being zero.
Evaluation at the first challenge is the first sumcheck's zero-valued cube sum.
-/

@[expose] public section

namespace Spartan.ZeroCheck

open MvPolynomial Realization

variable {R : Type} [CommRing R] (pp : PublicParams)

/-- The residual interpolation. Sparse polynomial materialization uses nonconstructive equality. -/
noncomputable def polynomial (x : R1CS.Statement R pp.toSizeR1CS)
    (oracles : ∀ i, OracleStatement (R := R) pp i) : MvPolynomial (Fin pp.ℓ_m) R :=
  Algebra.residualMLE (fun i => oracles (.inl i)) (R1CS.𝕫 x (oracles (.inr 0)))

/-- The public input and attached witness satisfy the retained R1CS matrices. -/
def inputRelation (x : R1CS.Statement R pp.toSizeR1CS)
    (oracles : ∀ i, OracleStatement (R := R) pp i) : Prop :=
  R1CS.relation R pp.toSizeR1CS x (fun i => oracles (.inl i)) (oracles (.inr 0))

/-- The residual interpolation vanishes at the retained challenge. -/
def outputRelation (stmt : (Fin pp.ℓ_m → R) × R1CS.Statement R pp.toSizeR1CS)
    (oracles : ∀ i, OracleStatement (R := R) pp i) : Prop :=
  eval stmt.1 (polynomial pp stmt.2 oracles) = 0

/-- The R1CS relation after witness attachment has a unique private witness. -/
def relIn : Set (((R1CS.Statement R pp.toSizeR1CS) ×
    (∀ i, OracleStatement (R := R) pp i)) × Unit) :=
  {s | inputRelation pp s.1.1 s.1.2}

/-- The first challenge establishes the initial zero-valued sumcheck claim. -/
def relOut : Set (((((Fin pp.ℓ_m → R) × R1CS.Statement R pp.toSizeR1CS) ×
    (∀ i, OracleStatement (R := R) pp i))) × Unit) :=
  {s | outputRelation pp s.1.1 s.1.2}

/-- The residual interpolation is zero exactly when the attached witness satisfies the R1CS. -/
theorem polynomial_zero_iff (x : R1CS.Statement R pp.toSizeR1CS)
    (oracles : ∀ i, OracleStatement (R := R) pp i) :
    polynomial pp x oracles = 0 ↔ inputRelation pp x oracles :=
  Algebra.residualMLE_zero_iff_r1cs (2 ^ pp.ℓ_w) pp.toSizeR1CS.n_w_le_n x
    (fun i => oracles (.inl i)) (oracles (.inr 0))

/-- The zero-check output is the first virtual polynomial's zero-valued cube sum. -/
theorem outputRelation_iff_firstVirtual
    (stmt : (Fin pp.ℓ_m → R) × R1CS.Statement R pp.toSizeR1CS)
    (oracles : ∀ i, OracleStatement (R := R) pp i) :
    outputRelation pp stmt oracles ↔
      Algebra.cubeSum (Algebra.firstVirtual (fun i => oracles (.inl i))
        (R1CS.𝕫 stmt.2 (oracles (.inr 0))) stmt.1) = 0 := by
  exact (congrArg (fun v : R => v = 0)
    (Algebra.firstVirtual_cubeSum_eq_residualMLE (m := pp.ℓ_m) (n := pp.ℓ_n)
      (fun i => oracles (.inl i)) (R1CS.𝕫 stmt.2 (oracles (.inr 0))) stmt.1)).to_iff.symm

/-- Each coordinate of the residual interpolation has degree at most one. -/
theorem polynomial_degree_le_one (x : R1CS.Statement R pp.toSizeR1CS)
    (oracles : ∀ i, OracleStatement (R := R) pp i) (i : Fin pp.ℓ_m) :
    degreeOf i (polynomial pp x oracles) ≤ 1 :=
  Algebra.residualMLE_degree_le_one _ _ i

end Spartan.ZeroCheck

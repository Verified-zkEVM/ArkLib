/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.EvalClaims

open Interaction.TwoParty

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

section SecondSumcheckView

variable (R : Type) [BEq R] [CommRing R] [IsDomain R] [Fintype R] [LawfulBEq R]
  [Nontrivial R] (pp : PublicParams)

/-- Materialize the multilinear extension of the concatenated R1CS vector as a
polynomial in the variable-index coordinates. -/
def zPolynomial
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp)) :
    CPoly.CMvPolynomial pp.ℓ_n R :=
  ∑ idx : Fin pp.toSizeR1CS.n_x ⊕ Fin pp.toSizeR1CS.n_w,
    match idx with
    | .inl i =>
        CPoly.CMvPolynomial.eqPolynomial
          (MvPolynomial.booleanPoint (R := R) pp.ℓ_n (publicFullIndex pp i)) *
          CPoly.CMvPolynomial.C (stmt i)
    | .inr i =>
        let wi : R :=
          OracleInterface.answer (oracleStmt (.inr ()))
            (MvPolynomial.booleanPoint (R := R) pp.ℓ_w i)
        CPoly.CMvPolynomial.eqPolynomial
          (MvPolynomial.booleanPoint (R := R) pp.ℓ_n (witnessFullIndex pp i)) *
          CPoly.CMvPolynomial.C wi

/-- The materialized R1CS vector polynomial agrees with concrete `z`
evaluation. -/
theorem zPolynomial_eval
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (point : Fin pp.ℓ_n → R) :
    CPoly.CMvPolynomial.eval point (zPolynomial R pp stmt oracleStmt) =
      zEvalFromOracleStmt (R := R) pp stmt oracleStmt point := by
  simp [zPolynomial, zEvalFromOracleStmt, MvPolynomial.eqWeight,
    CPoly.CMvPolynomial.eval_eqPolynomial]

/-- The materialized R1CS vector polynomial is multilinear. -/
theorem zPolynomial_degreeOf
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (i : Fin pp.ℓ_n) :
    CPoly.CMvPolynomial.degreeOf i (zPolynomial R pp stmt oracleStmt) ≤ 1 := by
  unfold zPolynomial
  calc
    _ ≤ (Finset.univ : Finset (Fin pp.toSizeR1CS.n_x ⊕ Fin pp.toSizeR1CS.n_w)).sup
        (fun idx =>
          CPoly.CMvPolynomial.degreeOf i
            (match idx with
            | .inl j =>
                CPoly.CMvPolynomial.eqPolynomial
                  (MvPolynomial.booleanPoint (R := R) pp.ℓ_n (publicFullIndex pp j)) *
                  CPoly.CMvPolynomial.C (stmt j)
            | .inr j =>
                let wj : R :=
                  OracleInterface.answer (oracleStmt (.inr ()))
                    (MvPolynomial.booleanPoint (R := R) pp.ℓ_w j)
                CPoly.CMvPolynomial.eqPolynomial
                  (MvPolynomial.booleanPoint (R := R) pp.ℓ_n (witnessFullIndex pp j)) *
                  CPoly.CMvPolynomial.C wj)) := by
      exact CPoly.CMvPolynomial.degreeOf_sum_le i _ _
    _ ≤ 1 := by
      apply Finset.sup_le
      intro idx _
      cases idx with
      | inl j =>
          calc
            _ ≤
                CPoly.CMvPolynomial.degreeOf i
                  (CPoly.CMvPolynomial.eqPolynomial
                    (MvPolynomial.booleanPoint (R := R) pp.ℓ_n (publicFullIndex pp j))) +
                  CPoly.CMvPolynomial.degreeOf i
                    (CPoly.CMvPolynomial.C (stmt j) : CPoly.CMvPolynomial pp.ℓ_n R) := by
              exact CPoly.CMvPolynomial.degreeOf_mul_le i _ _
            _ ≤ 1 + 0 := by
              gcongr
              · exact CPoly.CMvPolynomial.eqPolynomial_degreeOf _ i
              · exact le_of_eq (CPoly.CMvPolynomial.degreeOf_C (S := R) _ _)
            _ = 1 := by norm_num
      | inr j =>
          let wj : R :=
            OracleInterface.answer (oracleStmt (.inr ()))
              (MvPolynomial.booleanPoint (R := R) pp.ℓ_w j)
          calc
            _ ≤
                CPoly.CMvPolynomial.degreeOf i
                  (CPoly.CMvPolynomial.eqPolynomial
                    (MvPolynomial.booleanPoint (R := R) pp.ℓ_n (witnessFullIndex pp j))) +
                  CPoly.CMvPolynomial.degreeOf i
                    (CPoly.CMvPolynomial.C wj : CPoly.CMvPolynomial pp.ℓ_n R) := by
              exact CPoly.CMvPolynomial.degreeOf_mul_le i _ _
            _ ≤ 1 + 0 := by
              gcongr
              · exact CPoly.CMvPolynomial.eqPolynomial_degreeOf _ i
              · exact le_of_eq (CPoly.CMvPolynomial.degreeOf_C (S := R) _ _)
            _ = 1 := by norm_num

/-- For a fixed constraint point, materialize a matrix multilinear extension as
a polynomial in the variable-index coordinates. -/
def matrixAtConstraintPolynomial
    (matrix : R1CS.MatrixIdx)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (constraintPoint : Fin pp.ℓ_m → R) :
    CPoly.CMvPolynomial pp.ℓ_n R :=
  ∑ constraintBits : Fin pp.ℓ_m → Fin 2,
    CPoly.CMvPolynomial.C
      (MvPolynomial.eval constraintPoint
        (MvPolynomial.eqPolynomial (constraintBits : Fin pp.ℓ_m → R))) *
      CPoly.CMvPolynomial.MLE'
        ((oracleStmt (.inl matrix)) (finFunctionFinEquiv constraintBits))

/-- Matrix multilinear extensions remain multilinear in the variable-index
coordinates after fixing the constraint point. -/
theorem matrixAtConstraintPolynomial_degreeOf
    (matrix : R1CS.MatrixIdx)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (constraintPoint : Fin pp.ℓ_m → R)
    (i : Fin pp.ℓ_n) :
    CPoly.CMvPolynomial.degreeOf i
      (matrixAtConstraintPolynomial R pp matrix oracleStmt constraintPoint) ≤ 1 := by
  unfold matrixAtConstraintPolynomial
  calc
    _ ≤ (Finset.univ : Finset (Fin pp.ℓ_m → Fin 2)).sup (fun constraintBits =>
        CPoly.CMvPolynomial.degreeOf i
          (CPoly.CMvPolynomial.C
            (MvPolynomial.eval constraintPoint
              (MvPolynomial.eqPolynomial (constraintBits : Fin pp.ℓ_m → R))) *
            CPoly.CMvPolynomial.MLE'
              ((oracleStmt (.inl matrix)) (finFunctionFinEquiv constraintBits)))) := by
      exact CPoly.CMvPolynomial.degreeOf_sum_le i _ _
    _ ≤ 1 := by
      apply Finset.sup_le
      intro constraintBits _
      calc
        _ ≤
            CPoly.CMvPolynomial.degreeOf i
              (CPoly.CMvPolynomial.C
                (MvPolynomial.eval constraintPoint
                  (MvPolynomial.eqPolynomial (constraintBits : Fin pp.ℓ_m → R))) :
                CPoly.CMvPolynomial pp.ℓ_n R) +
            CPoly.CMvPolynomial.degreeOf i
              (CPoly.CMvPolynomial.MLE'
                ((oracleStmt (.inl matrix)) (finFunctionFinEquiv constraintBits))) := by
          exact CPoly.CMvPolynomial.degreeOf_mul_le i _ _
        _ ≤ 0 + 1 := by
          gcongr
          · exact le_of_eq (CPoly.CMvPolynomial.degreeOf_C (S := R) _ _)
          · exact CPoly.CMvPolynomial.MLE'_degreeOf _ i
        _ = 1 := by norm_num

/-- The materialized fixed-row matrix polynomial agrees with the native matrix
oracle answer. -/
theorem matrixAtConstraintPolynomial_eval
    (matrix : R1CS.MatrixIdx)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (constraintPoint : Fin pp.ℓ_m → R)
    (variablePoint : Fin pp.ℓ_n → R) :
    CPoly.CMvPolynomial.eval variablePoint
        (matrixAtConstraintPolynomial R pp matrix oracleStmt constraintPoint) =
      OracleInterface.answer (oracleStmt (.inl matrix))
        (constraintPoint, variablePoint) := by
  let A := oracleStmt (.inl matrix)
  change CPoly.CMvPolynomial.eval variablePoint
      (∑ constraintBits : Fin pp.ℓ_m → Fin 2,
        CPoly.CMvPolynomial.C
          (MvPolynomial.eval constraintPoint
            (MvPolynomial.eqPolynomial (constraintBits : Fin pp.ℓ_m → R))) *
          CPoly.CMvPolynomial.MLE' (A (finFunctionFinEquiv constraintBits))) =
    MvPolynomial.eval variablePoint
      (MvPolynomial.eval (MvPolynomial.C ∘ constraintPoint) A.toMLE)
  have hMLE :
      ∀ row : Fin pp.toSizeR1CS.n → R,
        CPoly.CMvPolynomial.eval variablePoint (CPoly.CMvPolynomial.MLE' row) =
          MvPolynomial.eval variablePoint (MvPolynomial.MLE' row) := by
    intro row
    rw [CPoly.eval_equiv, CPoly.CMvPolynomial.fromCMvPolynomial_MLE']
  simp [Matrix.toMLE, MvPolynomial.MLE', MvPolynomial.MLE,
    MvPolynomial.eqPolynomial_expanded, hMLE]

/-- The claim checked by the second sum-check: the verifier's random linear
combination of the three matrix-vector evaluation claims. -/
def secondSumcheckTarget
    (state : AfterLinearCombinationStatement R pp) :
    SecondSumcheckClaim R :=
  match state.2.2.1 with
  | none => 0
  | some _ => ∑ matrix : R1CS.MatrixIdx, state.1 matrix * state.2.1 matrix

/-- Evaluate the second virtual sum-check polynomial using verifier-side
queries to the Spartan matrix and witness oracle family. -/
def secondSumcheckEvalByQueries
    (state : AfterLinearCombinationStatement R pp)
    (variablePoint : Fin pp.ℓ_n → R) :
    OracleComp [WithWitnessOracleFamily R pp]ₒ R :=
  match state.2.2.1 with
  | none => pure 0
  | some first => do
      let stmt := state.2.2.2.2
      let z ← zEvalByQueries (R := R) pp stmt variablePoint
      let a : R ← liftM <|
        ([WithWitnessOracleFamily R pp]ₒ).query ⟨.inl .A, (first.point, variablePoint)⟩
      let b : R ← liftM <|
        ([WithWitnessOracleFamily R pp]ₒ).query ⟨.inl .B, (first.point, variablePoint)⟩
      let c : R ← liftM <|
        ([WithWitnessOracleFamily R pp]ₒ).query ⟨.inl .C, (first.point, variablePoint)⟩
      pure <| (state.1 .A * a + state.1 .B * b + state.1 .C * c) * z

/-- Query evaluator for Spartan's second virtual sum-check polynomial. -/
def simulateSecondSumcheckOracle
    (state : AfterLinearCombinationStatement R pp) :
    QueryImpl [SecondSumcheckOracleFamily R pp]ₒ
      (OracleComp [WithWitnessOracleFamily R pp]ₒ)
  | ⟨(), point⟩ => secondSumcheckEvalByQueries (R := R) pp state point

/-- Materializer for the second virtual sum-check oracle. -/
abbrev SecondSumcheckOracleMaterializer : Type :=
  AfterLinearCombinationStatement R pp →
    OracleStatement (WithWitnessOracleFamily R pp) →
      OracleStatement (SecondSumcheckOracleFamily R pp)

/-- A second-sumcheck materializer agrees pointwise with verifier-side query
routing through the post-linear-combination Spartan oracle family. -/
def SecondSumcheckOracleMaterializer.Realizes
    (materialize : SecondSumcheckOracleMaterializer R pp) : Prop :=
  ∀ state oracleStmt point,
    simulateQ
      (OracleInterface.toOracleImpl (WithWitnessOracleFamily R pp) oracleStmt)
      (secondSumcheckEvalByQueries (R := R) pp state point) =
      pure (OracleInterface.answer (materialize state oracleStmt ()) point)

/-- Computable polynomial expression for Spartan's second virtual sum-check
polynomial in the variable-index coordinates. -/
def secondSumcheckPolynomialExpr
    (state : AfterLinearCombinationStatement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp)) :
    CPoly.CMvPolynomial pp.ℓ_n R :=
  match state.2.2.1 with
  | none => CPoly.CMvPolynomial.C 0
  | some first =>
      let stmt := state.2.2.2.2
      let weightedMatrix :=
        ∑ matrix : R1CS.MatrixIdx,
          CPoly.CMvPolynomial.C (state.1 matrix) *
            matrixAtConstraintPolynomial R pp matrix oracleStmt first.point
      weightedMatrix * zPolynomial R pp stmt oracleStmt

/-- Spartan's second virtual sum-check polynomial has individual degree at most
two in every variable-index coordinate. -/
theorem secondSumcheckPolynomialExpr_degreeOf
    (state : AfterLinearCombinationStatement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (i : Fin pp.ℓ_n) :
    CPoly.CMvPolynomial.degreeOf i (secondSumcheckPolynomialExpr R pp state oracleStmt) ≤
      secondSumcheckDegree := by
  cases hFirst : state.2.2.1 with
  | none =>
      calc
        CPoly.CMvPolynomial.degreeOf i (secondSumcheckPolynomialExpr R pp state oracleStmt) =
            0 := by
          simpa [secondSumcheckPolynomialExpr, hFirst] using
            CPoly.CMvPolynomial.degreeOf_C (S := R) (0 : R) i
        _ ≤ secondSumcheckDegree := by
          simp [secondSumcheckDegree]
  | some first =>
    calc
      _ ≤
          CPoly.CMvPolynomial.degreeOf i
            (∑ matrix : R1CS.MatrixIdx,
              CPoly.CMvPolynomial.C (state.1 matrix) *
                matrixAtConstraintPolynomial R pp matrix oracleStmt first.point) +
          CPoly.CMvPolynomial.degreeOf i
            (zPolynomial R pp state.2.2.2.2 oracleStmt) := by
        simp only [secondSumcheckPolynomialExpr, hFirst]
        exact CPoly.CMvPolynomial.degreeOf_mul_le i _ _
      _ ≤ 1 + 1 := by
        gcongr
        · calc
            _ ≤ (Finset.univ : Finset R1CS.MatrixIdx).sup (fun matrix =>
                CPoly.CMvPolynomial.degreeOf i
                  (CPoly.CMvPolynomial.C (state.1 matrix) *
                    matrixAtConstraintPolynomial R pp matrix oracleStmt first.point)) := by
              exact CPoly.CMvPolynomial.degreeOf_sum_le i _ _
            _ ≤ 1 := by
              apply Finset.sup_le
              intro matrix _
              calc
                _ ≤
                    CPoly.CMvPolynomial.degreeOf i
                      (CPoly.CMvPolynomial.C (state.1 matrix) : CPoly.CMvPolynomial pp.ℓ_n R) +
                    CPoly.CMvPolynomial.degreeOf i
                      (matrixAtConstraintPolynomial R pp matrix oracleStmt
                        first.point) := by
                  exact CPoly.CMvPolynomial.degreeOf_mul_le i _ _
                _ ≤ 0 + 1 := by
                  gcongr
                  · exact le_of_eq (CPoly.CMvPolynomial.degreeOf_C (S := R) _ _)
                  · exact matrixAtConstraintPolynomial_degreeOf R pp matrix oracleStmt _ i
                _ = 1 := by norm_num
        · exact zPolynomial_degreeOf R pp state.2.2.2.2 oracleStmt i
      _ = 2 := by norm_num

/-- Spartan's second virtual sum-check polynomial packaged as a CompPoly
degree-bounded oracle statement. -/
def secondSumcheckPolynomial
    (state : AfterLinearCombinationStatement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp)) :
    SecondSumcheckOracle R pp :=
  ⟨secondSumcheckPolynomialExpr R pp state oracleStmt,
    CPoly.CMvPolynomial.individualDegreeLE_of_degreeOf_le
      (secondSumcheckPolynomialExpr R pp state oracleStmt)
      (secondSumcheckPolynomialExpr_degreeOf R pp state oracleStmt)⟩

/-- Canonical materializer for Spartan's second virtual sum-check oracle. -/
def secondSumcheckOracleMaterializer : SecondSumcheckOracleMaterializer R pp :=
  fun state oracleStmt _ => secondSumcheckPolynomial R pp state oracleStmt

/-- The canonical second-sumcheck materializer realizes the verifier-side query
routing through the Spartan oracle statement. -/
theorem secondSumcheckOracleMaterializer_realizes :
    (secondSumcheckOracleMaterializer R pp).Realizes := by
  intro state oracleStmt point
  change
    simulateQ
        (OracleInterface.toOracleImpl (WithWitnessOracleFamily R pp) oracleStmt)
        (secondSumcheckEvalByQueries (R := R) pp state point) =
      pure (CPoly.CMvPolynomial.eval point
        (secondSumcheckPolynomialExpr R pp state oracleStmt))
  cases hFirst : state.2.2.1 with
  | none =>
      simp [secondSumcheckEvalByQueries, secondSumcheckPolynomialExpr, hFirst]
  | some first =>
      simp [secondSumcheckEvalByQueries, secondSumcheckPolynomialExpr, hFirst,
        simulateQ_zEvalByQueries, matrixAtConstraintPolynomial_eval, zPolynomial_eval,
        OracleInterface.toOracleImpl]
      rfl

end SecondSumcheckView

section SecondSumcheckBoundary

variable (R : Type) [BEq R] [CommRing R] [instDomain : IsDomain R] [instFintype : Fintype R]
  [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Sum-check context used for Spartan's second virtual polynomial. -/
abbrev secondSumcheckContext : Interaction.Oracle.Spec :=
  Sumcheck.context R secondSumcheckDegree pp.ℓ_n

/-- Role decoration for Spartan's second sum-check. -/
abbrev secondSumcheckRoles :
    Interaction.Oracle.Spec.RoleDeco (secondSumcheckContext R pp) :=
  Sumcheck.roles R secondSumcheckDegree pp.ℓ_n

/-- Oracle-message decoration for Spartan's second sum-check. -/
abbrev secondSumcheckOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (secondSumcheckContext R pp) :=
  Sumcheck.oracleDeco R secondSumcheckDegree pp.ℓ_n

/-- Boundary projection from Spartan's post-linear-combination state to the
second sum-check claim. -/
def secondSumcheckStatementProjection :
    Interaction.Boundary.OracleStatementProjection
      (AfterLinearCombinationStatement R pp)
      (SecondSumcheckClaim R)
      (fun _ => secondSumcheckContext R pp) where
  proj := secondSumcheckTarget R pp

/-- Lift the second sum-check verifier result back into the Spartan state. -/
def secondSumcheckStatementLift :
    Interaction.Boundary.OracleStatementLift
      (secondSumcheckStatementProjection R pp)
      (fun _ _ => Option (SecondSumcheckResult R pp))
      (fun _ _ => AfterSecondSumcheckStatement R pp) where
  lift := fun outer _ result => ⟨result, outer⟩

/-- Oracle-access boundary for Spartan's second virtual sum-check polynomial. -/
def secondSumcheckOracleAccess
    (state : AfterLinearCombinationStatement R pp) :
    Interaction.Boundary.OracleStatementAccess
      (InnerContext := secondSumcheckContext R pp)
      (WithWitnessOracleFamily R pp)
      (SecondSumcheckOracleFamily R pp)
      (fun _ => SecondSumcheckOracleFamily R pp)
      (fun _ => AfterSecondSumcheckOracleFamily R pp) where
  simulateIn :=
    simulateSecondSumcheckOracle (R := R) pp state
  simulateOut := fun _ q =>
    liftM <| ([WithWitnessOracleFamily R pp]ₒ).query q

/-- Concrete materialization for the second virtual sum-check oracle boundary. -/
def secondSumcheckOracleReification
    (state : AfterLinearCombinationStatement R pp) :
    Interaction.Boundary.OracleStatementReification
      (InnerContext := secondSumcheckContext R pp)
      (WithWitnessOracleFamily R pp)
      (SecondSumcheckOracleFamily R pp)
      (fun _ => SecondSumcheckOracleFamily R pp)
      (fun _ => AfterSecondSumcheckOracleFamily R pp) where
  materializeIn := secondSumcheckOracleMaterializer R pp state
  materializeOut := fun outer _ _ => outer

/-- The concrete second-sumcheck materialization realizes the verifier-side
query routing. -/
lemma secondSumcheckOracleReification_realizes
    (state : AfterLinearCombinationStatement R pp) :
    Interaction.Boundary.OracleStatementReification.Realizes
      (secondSumcheckOracleAccess R pp state)
      (secondSumcheckOracleReification R pp state) := by
  constructor
  · intro oStmtIn i point
    cases i
    exact secondSumcheckOracleMaterializer_realizes R pp state oStmtIn point
  · intro oStmtIn _ _ i q
    rfl

/-- Bundled oracle boundary for Spartan's second virtual sum-check. -/
def secondSumcheckBoundary :
    Interaction.Boundary.OracleStatement
      (secondSumcheckStatementLift R pp)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => SecondSumcheckOracleFamily R pp)
      (fun _ _ => SecondSumcheckOracleFamily R pp)
      (fun _ _ => AfterSecondSumcheckOracleFamily R pp) where
  access := fun outer => secondSumcheckOracleAccess R pp outer
  reification := fun outer => secondSumcheckOracleReification R pp outer
  coherent := fun outer =>
    secondSumcheckOracleReification_realizes R pp outer

/-- Full statement-and-witness transport for the second virtual sum-check
boundary. The bounded-degree polynomial is materialized by the oracle boundary,
so the inner sum-check witness is trivial. -/
def secondSumcheckContextLift :
    Interaction.Boundary.OracleContextLift
      (secondSumcheckStatementProjection R pp)
      PUnit
      PUnit
      (fun _ _ => Option (SecondSumcheckResult R pp))
      (fun _ _ => AfterSecondSumcheckStatement R pp)
      (fun _ _ => PUnit)
      (fun _ _ => PUnit) where
  witProj := {
    proj := fun _ _ => PUnit.unit
  }
  stmt := secondSumcheckStatementLift R pp
  wit := {
    lift := fun _ _ _ _ _ => PUnit.unit
  }

/-- Bundled oracle context boundary for Spartan's second virtual sum-check. -/
def secondSumcheckContextBoundary :
    Interaction.Boundary.OracleContext
      (secondSumcheckContextLift R pp)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => SecondSumcheckOracleFamily R pp)
      (fun _ _ => SecondSumcheckOracleFamily R pp)
      (fun _ _ => AfterSecondSumcheckOracleFamily R pp) where
  access := fun outer => secondSumcheckOracleAccess R pp outer
  reification := fun outer => secondSumcheckOracleReification R pp outer
  coherent := fun outer =>
    secondSumcheckOracleReification_realizes R pp outer

/-- Spartan's second sum-check reduction as a boundary around the generic
sum-check reduction. -/
def secondSumcheckReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [IsDomain R] [Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec
      (AfterLinearCombinationStatement R pp)
      (fun _ => secondSumcheckContext R pp)
      (fun _ => secondSumcheckRoles R pp)
      (fun _ => secondSumcheckOracleDeco R pp)
      (fun _ => PUnit)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => PUnit)
      (fun _ _ => AfterSecondSumcheckStatement R pp)
      (fun _ _ => AfterSecondSumcheckOracleFamily R pp)
      (fun _ _ => PUnit) :=
  Interaction.Oracle.Reduction.pullback
    (secondSumcheckContextLift R pp)
    (secondSumcheckContextBoundary R pp)
    (Sumcheck.reduction (R := R) (deg := secondSumcheckDegree)
      (D := D) sampleChallenge pp.ℓ_n)

/-- Spartan's second sum-check in continuation form. -/
def secondSumcheckContinuationReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [IsDomain R] [Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => secondSumcheckContext R pp)
      (fun _ => secondSumcheckRoles R pp)
      (fun _ => secondSumcheckOracleDeco R pp)
      (fun _ => AfterLinearCombinationStatement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => PUnit)
      (fun _ _ => AfterSecondSumcheckStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterSecondSumcheckOracleFamily R pp)
      (fun _ _ => PUnit) where
  prover _ sWithOracles witness := do
    let state := sWithOracles.stmt
    let strat ←
      (secondSumcheckReduction (R := R) (pp := pp) D sampleChallenge).prover
        state
        ⟨PUnit.unit, sWithOracles.oracleStmt⟩
        witness
    pure <|
      Interaction.Spec.ShapeOver.mapOutput focalMonadicShape
        (agent := PUnit.unit)
        (spec := (secondSumcheckContext R pp).toInteractionSpec)
        (ctxs := RoleDecoration.withMonads
          ((secondSumcheckContext R pp).toSpecRoles (secondSumcheckRoles R pp))
          ((secondSumcheckContext R pp).toProverMonadDecoration oSpec))
        (fun _ out =>
          (⟨⟨out.stmt.stmt, out.stmt.oracleStmt⟩, out.wit⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => AfterSecondSumcheckStatement R pp)
                (fun _ => AfterSecondSumcheckOracleFamily R pp)
                PUnit.unit)
              PUnit))
        strat
  verifier := {
    toFun := fun _ state =>
      (secondSumcheckReduction (R := R) (pp := pp) D sampleChallenge).verifier.toFun
        state PUnit.unit
    simulate := fun _ _ q =>
      liftM <| ([WithWitnessOracleFamily R pp]ₒ).query q
  }

end SecondSumcheckBoundary

end

end OracleLayer

end Spartan


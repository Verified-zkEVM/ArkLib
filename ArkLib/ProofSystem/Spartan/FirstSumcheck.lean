/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.OracleInterfaces
import ArkLib.Data.Fin.Basic
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Interaction.Boundary.Reification

open Interaction.TwoParty

open MvPolynomial Matrix
open Interaction OracleComp OracleSpec
open scoped BigOperators

namespace Spartan

namespace OracleLayer

noncomputable section

/-- Simulating a finite dependent traversal whose entries all reduce to pure
values reduces to the pure dependent function.

This is the finite-family analogue of `simulateQ_map`: query routing can be
proved pointwise, then lifted through the `Fin`-indexed traversal used by
Spartan's concrete oracle evaluators. -/
theorem simulateQ_fin_traverseM_pure
    {ι : Type _} {spec : OracleSpec ι} {n : ℕ}
    {β : Fin n → Type _}
    (impl : QueryImpl spec Id)
    (f : (i : Fin n) → OracleComp spec (β i))
    (g : (i : Fin n) → β i)
    (h : ∀ i, simulateQ impl (f i) = pure (g i)) :
    simulateQ impl (Fin.traverseM f) = pure g := by
  induction n with
  | zero =>
      rw [Fin.traverseM_zero]
      simp
      ext i
      exact i.elim0
  | succ n ih =>
      rw [Fin.traverseM_succ, simulateQ_bind]
      rw [ih
        (β := fun i : Fin n => β i.castSucc)
        (f := fun i => f i.castSucc)
        (g := fun i => g i.castSucc)]
      · simp only [bind_pure_comp, simulateQ_map, pure_bind]
        rw [h (Fin.last n)]
        change Fin.snoc (Fin.init g) (g (Fin.last n)) = g
        rw [Fin.snoc_init_self]
      · intro i
        exact h i.castSucc

section FirstSumcheckView

variable (R : Type) [BEq R] [CommRing R] [IsDomain R] [Fintype R] [LawfulBEq R]
  [Nontrivial R] (pp : PublicParams)

/-- Embed a public-input coordinate into the full padded R1CS vector index. -/
def publicFullIndex (i : Fin pp.toSizeR1CS.n_x) :
    Fin pp.toSizeR1CS.n :=
  ⟨i.1, lt_of_lt_of_le i.2 (by simp [R1CS.Size.n_x])⟩

/-- Embed a witness coordinate into the full padded R1CS vector index. -/
def witnessFullIndex (i : Fin pp.toSizeR1CS.n_w) :
    Fin pp.toSizeR1CS.n :=
  ⟨pp.toSizeR1CS.n_x + i.1, by
    have hn := pp.toSizeR1CS.n_w_le_n
    have hi := i.2
    simp [R1CS.Size.n_x] at hi ⊢
    omega⟩

/-- Evaluate the multilinear extension of the concatenated R1CS vector using
the public statement and queries to the witness oracle. -/
def zEvalByQueries
    (stmt : Statement R pp) (point : Fin pp.ℓ_n → R) :
    OracleComp [WithWitnessOracleFamily R pp]ₒ R := do
  let publicPart :=
    ∑ i : Fin pp.toSizeR1CS.n_x,
      MvPolynomial.eqWeight (R := R) point (publicFullIndex pp i) * stmt i
  let witnessTerms ← Fin.traverseM fun i : Fin pp.toSizeR1CS.n_w => do
    let wi : R ← liftM <|
      ([WithWitnessOracleFamily R pp]ₒ).query
        ⟨.inr (), MvPolynomial.booleanPoint (R := R) pp.ℓ_w i⟩
    pure <| MvPolynomial.eqWeight (R := R) point (witnessFullIndex pp i) * wi
  pure <| publicPart + ∑ i : Fin pp.toSizeR1CS.n_w, witnessTerms i

/-- Evaluate `M z` at a constraint point using queries to the matrix oracle and
the derived `z` evaluator. -/
def matrixVecEvalByQueries
    (matrix : R1CS.MatrixIdx) (stmt : Statement R pp)
    (constraintPoint : Fin pp.ℓ_m → R) :
    OracleComp [WithWitnessOracleFamily R pp]ₒ R := do
  let terms ← Fin.traverseM fun i : Fin pp.toSizeR1CS.n => do
    let variablePoint := MvPolynomial.booleanPoint (R := R) pp.ℓ_n i
    let matrixValue : R ← liftM <|
      ([WithWitnessOracleFamily R pp]ₒ).query
        ⟨.inl matrix, (constraintPoint, variablePoint)⟩
    let zValue ← zEvalByQueries (R := R) pp stmt variablePoint
    pure <| matrixValue * zValue
  pure <| ∑ i : Fin pp.toSizeR1CS.n, terms i

/-- Query evaluator for Spartan's first virtual sum-check polynomial. -/
def firstSumcheckEvalByQueries
    (state : AfterFirstChallengeStatement R pp)
    (constraintPoint : Fin pp.ℓ_m → R) :
    OracleComp [WithWitnessOracleFamily R pp]ₒ R := do
  let τ := state.1
  let stmt := state.2
  let a ← matrixVecEvalByQueries (R := R) pp .A stmt constraintPoint
  let b ← matrixVecEvalByQueries (R := R) pp .B stmt constraintPoint
  let c ← matrixVecEvalByQueries (R := R) pp .C stmt constraintPoint
  pure <| CPoly.CMvPolynomial.eval constraintPoint
    (CPoly.CMvPolynomial.eqPolynomial τ) * (a * b - c)

/-- Simulate queries to the first virtual sum-check oracle using the post-setup
R1CS matrix and witness oracle family. -/
def simulateFirstSumcheckOracle
    (state : AfterFirstChallengeStatement R pp) :
    QueryImpl [FirstSumcheckOracleFamily R pp]ₒ
      (OracleComp [WithWitnessOracleFamily R pp]ₒ)
  | ⟨(), point⟩ => firstSumcheckEvalByQueries (R := R) pp state point

/-- Materializer for the first virtual sum-check oracle.

This is the soundness-relevant hook: the materialized oracle statement is a
degree-bounded polynomial, while `firstSumcheckEvalByQueries` describes how its
evaluations are routed back to the post-setup Spartan oracle family. -/
abbrev FirstSumcheckOracleMaterializer : Type :=
  AfterFirstChallengeStatement R pp →
    OracleStatement (WithWitnessOracleFamily R pp) →
      OracleStatement (FirstSumcheckOracleFamily R pp)

/-- A first-sumcheck materializer agrees pointwise with verifier-side query
routing through the post-setup Spartan oracle family. -/
def FirstSumcheckOracleMaterializer.Realizes
    (materialize : FirstSumcheckOracleMaterializer R pp) : Prop :=
  ∀ state oracleStmt point,
    simulateQ
      (OracleInterface.toOracleImpl (WithWitnessOracleFamily R pp) oracleStmt)
      (firstSumcheckEvalByQueries (R := R) pp state point) =
      pure (OracleInterface.answer (materialize state oracleStmt ()) point)

/-- Evaluate the multilinear extension of the concatenated public-input and
witness vector against a concrete oracle statement. -/
def zEvalFromOracleStmt
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (point : Fin pp.ℓ_n → R) : R :=
  let publicPart :=
    ∑ i : Fin pp.toSizeR1CS.n_x,
      MvPolynomial.eqWeight (R := R) point (publicFullIndex pp i) * stmt i
  let witnessPart :=
    ∑ i : Fin pp.toSizeR1CS.n_w,
      let wi : R :=
        OracleInterface.answer (oracleStmt (.inr ()))
          (MvPolynomial.booleanPoint (R := R) pp.ℓ_w i)
      MvPolynomial.eqWeight (R := R) point (witnessFullIndex pp i) * wi
  publicPart + witnessPart

/-- For a fixed R1CS variable point, materialize the matrix multilinear
extension as a polynomial in the constraint-index variables. -/
def matrixEvalPolynomial
    (matrix : R1CS.MatrixIdx)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (variablePoint : Fin pp.ℓ_n → R) :
    CPoly.CMvPolynomial pp.ℓ_m R :=
  CPoly.CMvPolynomial.MLE' fun constraintIdx =>
    MvPolynomial.eval variablePoint
      (MvPolynomial.MLE' ((oracleStmt (.inl matrix)) constraintIdx))

/-- Matrix multilinear extensions are multilinear in the constraint-index
variables after fixing the R1CS variable point. -/
theorem matrixEvalPolynomial_degreeOf
    (matrix : R1CS.MatrixIdx)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (variablePoint : Fin pp.ℓ_n → R)
    (i : Fin pp.ℓ_m) :
    CPoly.CMvPolynomial.degreeOf i (matrixEvalPolynomial R pp matrix oracleStmt variablePoint) ≤ 1 := by
  unfold matrixEvalPolynomial
  exact CPoly.CMvPolynomial.MLE'_degreeOf _ _

/-- The materialized matrix polynomial agrees with the matrix oracle's native
multilinear-extension answer at every constraint point. -/
theorem matrixEvalPolynomial_eval
    (matrix : R1CS.MatrixIdx)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (constraintPoint : Fin pp.ℓ_m → R)
    (variablePoint : Fin pp.ℓ_n → R) :
    CPoly.CMvPolynomial.eval constraintPoint
        (matrixEvalPolynomial R pp matrix oracleStmt variablePoint) =
      OracleInterface.answer (oracleStmt (.inl matrix))
        (constraintPoint, variablePoint) := by
  let A := oracleStmt (.inl matrix)
  change CPoly.CMvPolynomial.eval constraintPoint
      (CPoly.CMvPolynomial.MLE' fun constraintIdx =>
        MvPolynomial.eval variablePoint (MvPolynomial.MLE' (A constraintIdx))) =
    MvPolynomial.eval variablePoint
      (MvPolynomial.eval (MvPolynomial.C ∘ constraintPoint) A.toMLE)
  rw [CPoly.eval_equiv, CPoly.CMvPolynomial.fromCMvPolynomial_MLE']
  have hMap :
      MvPolynomial.map (MvPolynomial.eval variablePoint) A.toMLE =
      MvPolynomial.MLE' fun constraintIdx =>
          MvPolynomial.eval variablePoint (MvPolynomial.MLE' (A constraintIdx)) := by
    simp [Matrix.toMLE, MvPolynomial.MLE', MvPolynomial.MLE,
      MvPolynomial.eqPolynomial_expanded]
  rw [MvPolynomial.map_eval, hMap]
  have hEval :
      MvPolynomial.eval constraintPoint =
        MvPolynomial.eval (MvPolynomial.eval variablePoint ∘ MvPolynomial.C ∘ constraintPoint) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp
  exact RingHom.congr_fun hEval _

/-- Materialize `M z` as a polynomial in the constraint-index variables, with
`z` evaluated from the concrete public statement and witness oracle. -/
def matrixVecPolynomial
    (matrix : R1CS.MatrixIdx)
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp)) :
    CPoly.CMvPolynomial pp.ℓ_m R :=
  ∑ i : Fin pp.toSizeR1CS.n,
    CPoly.CMvPolynomial.C
      (zEvalFromOracleStmt (R := R) pp stmt oracleStmt
        (MvPolynomial.booleanPoint (R := R) pp.ℓ_n i)) *
      matrixEvalPolynomial (R := R) pp matrix oracleStmt
        (MvPolynomial.booleanPoint (R := R) pp.ℓ_n i)

/-- `M z` is multilinear in the constraint-index variables. -/
theorem matrixVecPolynomial_degreeOf
    (matrix : R1CS.MatrixIdx)
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (i : Fin pp.ℓ_m) :
    CPoly.CMvPolynomial.degreeOf i (matrixVecPolynomial R pp matrix stmt oracleStmt) ≤ 1 := by
  unfold matrixVecPolynomial
  calc
    _ ≤ (Finset.univ : Finset (Fin pp.toSizeR1CS.n)).sup (fun j =>
        CPoly.CMvPolynomial.degreeOf i
          (CPoly.CMvPolynomial.C
            (zEvalFromOracleStmt (R := R) pp stmt oracleStmt
              (MvPolynomial.booleanPoint (R := R) pp.ℓ_n j)) *
            matrixEvalPolynomial (R := R) pp matrix oracleStmt
              (MvPolynomial.booleanPoint (R := R) pp.ℓ_n j))) := by
      exact CPoly.CMvPolynomial.degreeOf_sum_le i _ _
    _ ≤ 1 := by
      apply Finset.sup_le
      intro j _
      calc
        _ ≤
            CPoly.CMvPolynomial.degreeOf i
              (CPoly.CMvPolynomial.C
                (zEvalFromOracleStmt (R := R) pp stmt oracleStmt
                  (MvPolynomial.booleanPoint (R := R) pp.ℓ_n j))) +
              CPoly.CMvPolynomial.degreeOf i
                (matrixEvalPolynomial (R := R) pp matrix oracleStmt
                  (MvPolynomial.booleanPoint (R := R) pp.ℓ_n j)) := by
          exact CPoly.CMvPolynomial.degreeOf_mul_le i _ _
        _ ≤ 0 + 1 := by
          gcongr
          · exact le_of_eq (CPoly.CMvPolynomial.degreeOf_C (S := R) _ _)
          · exact matrixEvalPolynomial_degreeOf R pp matrix oracleStmt _ i
        _ = 1 := by norm_num

/-- Computable polynomial expression for Spartan's first virtual sum-check
polynomial. -/
def firstSumcheckPolynomialExpr
    (state : AfterFirstChallengeStatement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp)) :
    CPoly.CMvPolynomial pp.ℓ_m R :=
  let τ := state.1
  let stmt := state.2
  let a := matrixVecPolynomial (R := R) pp .A stmt oracleStmt
  let b := matrixVecPolynomial (R := R) pp .B stmt oracleStmt
  let c := matrixVecPolynomial (R := R) pp .C stmt oracleStmt
  CPoly.CMvPolynomial.eqPolynomial τ * (a * b - c)

/-- Spartan's first virtual sum-check polynomial has individual degree at most
three in every constraint-index variable. -/
theorem firstSumcheckPolynomialExpr_degreeOf
    (state : AfterFirstChallengeStatement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (i : Fin pp.ℓ_m) :
    CPoly.CMvPolynomial.degreeOf i (firstSumcheckPolynomialExpr R pp state oracleStmt) ≤
      firstSumcheckDegree := by
  unfold firstSumcheckPolynomialExpr firstSumcheckDegree
  dsimp only
  calc
    _ ≤ CPoly.CMvPolynomial.degreeOf i (CPoly.CMvPolynomial.eqPolynomial state.1) +
        CPoly.CMvPolynomial.degreeOf i
          (matrixVecPolynomial R pp .A state.2 oracleStmt *
            matrixVecPolynomial R pp .B state.2 oracleStmt -
              matrixVecPolynomial R pp .C state.2 oracleStmt) := by
      exact CPoly.CMvPolynomial.degreeOf_mul_le i _ _
    _ ≤ 1 + 2 := by
      gcongr
      · exact CPoly.CMvPolynomial.eqPolynomial_degreeOf state.1 i
      · calc
          _ ≤ max
              (CPoly.CMvPolynomial.degreeOf i
                (matrixVecPolynomial R pp .A state.2 oracleStmt *
                  matrixVecPolynomial R pp .B state.2 oracleStmt))
              (CPoly.CMvPolynomial.degreeOf i
                (matrixVecPolynomial R pp .C state.2 oracleStmt)) := by
            exact CPoly.CMvPolynomial.degreeOf_sub_le i _ _
          _ ≤ max (1 + 1) 1 := by
            gcongr
            · calc
                _ ≤ CPoly.CMvPolynomial.degreeOf i (matrixVecPolynomial R pp .A state.2 oracleStmt) +
                    CPoly.CMvPolynomial.degreeOf i (matrixVecPolynomial R pp .B state.2 oracleStmt) := by
                  exact CPoly.CMvPolynomial.degreeOf_mul_le i _ _
                _ ≤ 1 + 1 := by
                  gcongr <;> exact matrixVecPolynomial_degreeOf R pp _ state.2 oracleStmt i
            · exact matrixVecPolynomial_degreeOf R pp .C state.2 oracleStmt i
          _ = 2 := by norm_num
    _ = 3 := by norm_num

/-- Spartan's first virtual sum-check polynomial packaged as a CompPoly
degree-bounded oracle statement. -/
def firstSumcheckPolynomial
    (state : AfterFirstChallengeStatement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp)) :
    FirstSumcheckOracle R pp :=
  ⟨firstSumcheckPolynomialExpr R pp state oracleStmt,
    CPoly.CMvPolynomial.individualDegreeLE_of_degreeOf_le
      (firstSumcheckPolynomialExpr R pp state oracleStmt)
      (firstSumcheckPolynomialExpr_degreeOf R pp state oracleStmt)⟩

/-- Canonical materializer for Spartan's first virtual sum-check oracle. -/
def firstSumcheckOracleMaterializer : FirstSumcheckOracleMaterializer R pp :=
  fun state oracleStmt _ => firstSumcheckPolynomial R pp state oracleStmt

/-- Simulating the query-based view of `z` against a concrete oracle statement
agrees with direct concrete evaluation. -/
theorem simulateQ_zEvalByQueries
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (point : Fin pp.ℓ_n → R) :
    simulateQ
      (OracleInterface.toOracleImpl (WithWitnessOracleFamily R pp) oracleStmt)
      (zEvalByQueries (R := R) pp stmt point) =
      pure (zEvalFromOracleStmt (R := R) pp stmt oracleStmt point) := by
  simp only [zEvalByQueries, zEvalFromOracleStmt, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_fin_traverseM_pure
    (g := fun i : Fin pp.toSizeR1CS.n_w =>
      let wi : R :=
        OracleInterface.answer (oracleStmt (.inr ()))
          (MvPolynomial.booleanPoint (R := R) pp.ℓ_w i)
      MvPolynomial.eqWeight (R := R) point (witnessFullIndex pp i) *
        wi)]
  · simp
  · intro i
    rfl

/-- Simulating the query-based view of `M z` agrees with evaluating the
materialized `M z` polynomial. -/
theorem simulateQ_matrixVecEvalByQueries
    (matrix : R1CS.MatrixIdx)
    (stmt : Statement R pp)
    (oracleStmt : OracleStatement (WithWitnessOracleFamily R pp))
    (constraintPoint : Fin pp.ℓ_m → R) :
    simulateQ
      (OracleInterface.toOracleImpl (WithWitnessOracleFamily R pp) oracleStmt)
      (matrixVecEvalByQueries (R := R) pp matrix stmt constraintPoint) =
      pure (CPoly.CMvPolynomial.eval constraintPoint
        (matrixVecPolynomial R pp matrix stmt oracleStmt)) := by
  simp only [matrixVecEvalByQueries, matrixVecPolynomial, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_fin_traverseM_pure
    (g := fun i : Fin pp.toSizeR1CS.n =>
      let matrixValue : R :=
        OracleInterface.answer (oracleStmt (.inl matrix))
          (constraintPoint, MvPolynomial.booleanPoint (R := R) pp.ℓ_n i)
      matrixValue *
        zEvalFromOracleStmt (R := R) pp stmt oracleStmt
          (MvPolynomial.booleanPoint (R := R) pp.ℓ_n i))]
  · simp [matrixEvalPolynomial_eval, mul_comm]
  · intro i
    simp [simulateQ_zEvalByQueries, OracleInterface.toOracleImpl]
    let matrixValue : R :=
      OracleInterface.answer (oracleStmt (.inl matrix))
        (constraintPoint, MvPolynomial.booleanPoint (R := R) pp.ℓ_n i)
    change
      matrixValue * zEvalFromOracleStmt (R := R) pp stmt oracleStmt
          (MvPolynomial.booleanPoint (R := R) pp.ℓ_n i) =
        matrixValue * zEvalFromOracleStmt (R := R) pp stmt oracleStmt
          (MvPolynomial.booleanPoint (R := R) pp.ℓ_n i)
    rfl

/-- The canonical first-sumcheck materializer realizes the verifier-side query
routing through the Spartan oracle statement. -/
theorem firstSumcheckOracleMaterializer_realizes :
    (firstSumcheckOracleMaterializer R pp).Realizes := by
  intro state oracleStmt point
  change
    simulateQ
        (OracleInterface.toOracleImpl (WithWitnessOracleFamily R pp) oracleStmt)
        (firstSumcheckEvalByQueries (R := R) pp state point) =
      pure (CPoly.CMvPolynomial.eval point
        (firstSumcheckPolynomialExpr R pp state oracleStmt))
  simp [firstSumcheckEvalByQueries, firstSumcheckPolynomialExpr,
    simulateQ_matrixVecEvalByQueries]

end FirstSumcheckView

section FirstSumcheckBoundary

variable (R : Type) [BEq R] [CommRing R] [instDomain : IsDomain R] [instFintype : Fintype R]
  [LawfulBEq R] [Nontrivial R]
variable (pp : PublicParams)

/-- Sum-check context used for Spartan's first virtual polynomial. -/
abbrev firstSumcheckContext : Interaction.Oracle.Spec :=
  Sumcheck.context R firstSumcheckDegree pp.ℓ_m

/-- Role decoration for Spartan's first sum-check. -/
abbrev firstSumcheckRoles :
    Interaction.Oracle.Spec.RoleDeco (firstSumcheckContext R pp) :=
  Sumcheck.roles R firstSumcheckDegree pp.ℓ_m

/-- Oracle-message decoration for Spartan's first sum-check. -/
abbrev firstSumcheckOracleDeco :
    Interaction.Oracle.Spec.OracleDeco (firstSumcheckContext R pp) :=
  Sumcheck.oracleDeco R firstSumcheckDegree pp.ℓ_m

/-- Boundary projection from Spartan's post-setup state to the zero sum-check
claim. -/
def firstSumcheckStatementProjection :
    Interaction.Boundary.OracleStatementProjection
      (AfterFirstChallengeStatement R pp)
      (FirstSumcheckClaim R)
      (fun _ => firstSumcheckContext R pp) where
  proj := fun _ => 0

/-- Lift the sum-check verifier result back into the Spartan state. -/
def firstSumcheckStatementLift :
    Interaction.Boundary.OracleStatementLift
      (firstSumcheckStatementProjection R pp)
      (fun _ _ => Option (FirstSumcheckResult R pp))
      (fun _ _ => AfterFirstSumcheckStatement R pp) where
  lift := fun outer _ result => ⟨result, outer⟩

/-- Oracle-access boundary for Spartan's first virtual sum-check polynomial.

Input queries to the inner singleton polynomial oracle are evaluated through the
post-setup matrix and witness oracle family. Output queries keep the original
Spartan oracle family available after the sum-check. -/
def firstSumcheckOracleAccess
    (state : AfterFirstChallengeStatement R pp) :
    Interaction.Boundary.OracleStatementAccess
      (InnerContext := firstSumcheckContext R pp)
      (WithWitnessOracleFamily R pp)
      (FirstSumcheckOracleFamily R pp)
      (fun _ => FirstSumcheckOracleFamily R pp)
      (fun _ => AfterFirstSumcheckOracleFamily R pp) where
  simulateIn :=
    simulateFirstSumcheckOracle (R := R) pp state
  simulateOut := fun _ q =>
    liftM <| ([WithWitnessOracleFamily R pp]ₒ).query q

/-- Concrete materialization for the first virtual sum-check oracle boundary.

The inner singleton oracle is the virtual first sum-check polynomial derived
from the Spartan state and outer oracle statement. The output oracle family is
the unchanged Spartan matrix-plus-witness family. -/
def firstSumcheckOracleReification
    (state : AfterFirstChallengeStatement R pp) :
    Interaction.Boundary.OracleStatementReification
      (InnerContext := firstSumcheckContext R pp)
      (WithWitnessOracleFamily R pp)
      (FirstSumcheckOracleFamily R pp)
      (fun _ => FirstSumcheckOracleFamily R pp)
      (fun _ => AfterFirstSumcheckOracleFamily R pp) where
  materializeIn := firstSumcheckOracleMaterializer R pp state
  materializeOut := fun outer _ _ => outer

/-- The concrete first-sumcheck materialization realizes the verifier-side
query routing. -/
lemma firstSumcheckOracleReification_realizes
    (state : AfterFirstChallengeStatement R pp) :
    Interaction.Boundary.OracleStatementReification.Realizes
      (firstSumcheckOracleAccess R pp state)
      (firstSumcheckOracleReification R pp state) := by
  constructor
  · intro oStmtIn i point
    cases i
    exact firstSumcheckOracleMaterializer_realizes R pp state oStmtIn point
  · intro oStmtIn _ _ i q
    rfl

/-- Bundled oracle boundary for Spartan's first virtual sum-check. -/
def firstSumcheckBoundary :
    Interaction.Boundary.OracleStatement
      (firstSumcheckStatementLift R pp)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => FirstSumcheckOracleFamily R pp)
      (fun _ _ => FirstSumcheckOracleFamily R pp)
      (fun _ _ => AfterFirstSumcheckOracleFamily R pp) where
  access := fun outer => firstSumcheckOracleAccess R pp outer
  reification := fun outer => firstSumcheckOracleReification R pp outer
  coherent := fun outer =>
    firstSumcheckOracleReification_realizes R pp outer

/-- Full statement-and-witness transport for the first virtual sum-check
boundary. Sum-check has no external polynomial witness; the bounded-degree
polynomial lives in the inner oracle statement materialized by the boundary. -/
def firstSumcheckContextLift :
    Interaction.Boundary.OracleContextLift
      (firstSumcheckStatementProjection R pp)
      PUnit
      PUnit
      (fun _ _ => Option (FirstSumcheckResult R pp))
      (fun _ _ => AfterFirstSumcheckStatement R pp)
      (fun _ _ => PUnit)
      (fun _ _ => PUnit) where
  witProj := {
    proj := fun _ _ => PUnit.unit
  }
  stmt := firstSumcheckStatementLift R pp
  wit := {
    lift := fun _ _ _ _ _ => PUnit.unit
  }

/-- Bundled oracle context boundary for Spartan's first virtual sum-check. -/
def firstSumcheckContextBoundary :
    Interaction.Boundary.OracleContext
      (firstSumcheckContextLift R pp)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => FirstSumcheckOracleFamily R pp)
      (fun _ _ => FirstSumcheckOracleFamily R pp)
      (fun _ _ => AfterFirstSumcheckOracleFamily R pp) where
  access := fun outer => firstSumcheckOracleAccess R pp outer
  reification := fun outer => firstSumcheckOracleReification R pp outer
  coherent := fun outer =>
    firstSumcheckOracleReification_realizes R pp outer

/-- Spartan's first sum-check reduction as a boundary around the generic
sum-check reduction.

The input oracle family is the post-setup Spartan oracle family. The inner
sum-check sees a singleton bounded-degree polynomial family, materialized by
the boundary and realized by the pointwise routing hypothesis. -/
def firstSumcheckReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [IsDomain R] [Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec
      (AfterFirstChallengeStatement R pp)
      (fun _ => firstSumcheckContext R pp)
      (fun _ => firstSumcheckRoles R pp)
      (fun _ => firstSumcheckOracleDeco R pp)
      (fun _ => PUnit)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => PUnit)
      (fun _ _ => AfterFirstSumcheckStatement R pp)
      (fun _ _ => AfterFirstSumcheckOracleFamily R pp)
      (fun _ _ => PUnit) :=
  Interaction.Oracle.Reduction.pullback
    (firstSumcheckContextLift R pp)
    (firstSumcheckContextBoundary R pp)
    (Sumcheck.reduction (R := R) (deg := firstSumcheckDegree)
      (D := D) sampleChallenge pp.ℓ_m)

/-- Spartan's first sum-check in continuation form, ready to follow a setup
reduction by ordinary sequential composition.

The post-setup Spartan state is the local input statement rather than the
ambient shared index. This is the shape consumed by `Reduction.comp`: the setup
prefix produces the state, then this reduction consumes it as its statement. -/
def firstSumcheckContinuationReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [IsDomain R] [Fintype R]
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Oracle.Reduction oSpec PUnit
      (fun _ => firstSumcheckContext R pp)
      (fun _ => firstSumcheckRoles R pp)
      (fun _ => firstSumcheckOracleDeco R pp)
      (fun _ => AfterFirstChallengeStatement R pp)
      (ιₛᵢ := fun _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ => WithWitnessOracleFamily R pp)
      (fun _ => PUnit)
      (fun _ _ => AfterFirstSumcheckStatement R pp)
      (ιₛₒ := fun _ _ => R1CS.MatrixIdx ⊕ Unit)
      (fun _ _ => AfterFirstSumcheckOracleFamily R pp)
      (fun _ _ => PUnit) where
  prover _ sWithOracles witness := do
    let state := sWithOracles.stmt
    let strat ←
      (firstSumcheckReduction (R := R) (pp := pp) D sampleChallenge).prover
        state
        ⟨PUnit.unit, sWithOracles.oracleStmt⟩
        witness
    pure <|
      Interaction.Spec.ShapeOver.mapOutput focalMonadicShape
        (agent := PUnit.unit)
        (spec := (firstSumcheckContext R pp).toInteractionSpec)
        (ctxs := RoleDecoration.withMonads
          ((firstSumcheckContext R pp).toSpecRoles (firstSumcheckRoles R pp))
          ((firstSumcheckContext R pp).toProverMonadDecoration oSpec))
        (fun _ out =>
          (⟨⟨out.stmt.stmt, out.stmt.oracleStmt⟩, out.wit⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => AfterFirstSumcheckStatement R pp)
                (fun _ => AfterFirstSumcheckOracleFamily R pp)
                PUnit.unit)
              PUnit))
        strat
  verifier := {
    toFun := fun _ state =>
      (firstSumcheckReduction (R := R) (pp := pp) D sampleChallenge).verifier.toFun
        state PUnit.unit
    simulate := fun _ _ q =>
      liftM <| ([WithWitnessOracleFamily R pp]ₒ).query q
  }

end FirstSumcheckBoundary

end

end OracleLayer

end Spartan


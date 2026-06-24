import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.ProofSystem.Logup.Common

/-!
# LogUp Sumcheck Polynomial

Construction of the concrete polynomial used by LogUp's embedded sumcheck, following Protocol 2 of
Haböck's LogUp paper (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

This file defines the polynomial `logupQPolynomial : MvPolynomial (Fin n) F` used as LogUp's
sumcheck instance after the outer phase.

It proves direct facts about this polynomial, namely:
* its individual-degree bound `degreeOf ≤ M + 3`,
* its agreement with `qOnHypercube` on the
Boolean hypercube, and
* its agreement with the final-query reconstruction at sumcheck's final point.
-/

namespace Logup

open scoped BigOperators

section QEvaluation

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M K : ℕ}

/-- The batched polynomial expression `Q` from paper equation (18), evaluated on a row `u ∈ H`. -/
noncomputable def qOnHypercube (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (xChallenge : F) (zChallenge : Fin n → F)
    (batchingScalars : Fin K → F) (u : (Fin n → Fin 2)) : F :=
  ∑ k : Fin K, (
    (helpers k) u +
      MvPolynomial.eval (u : Fin n → F) (MvPolynomial.eqPolynomial zChallenge) *
        batchingScalars k *
        domainIdentityTerm groups oStmt multiplicity helpers xChallenge k u)

/-- Denominator term at the final sumcheck point, reconstructed from oracle query answers. -/
def phiAtPoint (xChallenge : F) (evals : PointEvaluations F M K) :
    InputOracleIdx M → F
  | .table => xChallenge + evals.table
  | .column i => xChallenge + evals.columns i

/-- Numerator term at the final sumcheck point, reconstructed from oracle query answers. -/
def numeratorAtPoint (evals : PointEvaluations F M K) : InputOracleIdx M → F
  | .table => evals.multiplicity
  | .column _ => -1

/-- Term denominator at the final sumcheck point, indexed by `0, ..., M`. -/
def termPhiAtPoint (xChallenge : F) (evals : PointEvaluations F M K) (i : TermIdx M) : F :=
  phiAtPoint xChallenge evals (termToInput i)

/-- Term numerator at the final sumcheck point, indexed by `0, ..., M`. -/
def termNumeratorAtPoint (evals : PointEvaluations F M K) (i : TermIdx M) : F :=
  numeratorAtPoint evals (termToInput i)

/-- The domain-identity expression at the final sumcheck point `r`. -/
noncomputable def domainIdentityAtPoint (groups : PartialSumGroups M K)
    (xChallenge : F) (evals : PointEvaluations F M K) (k : Fin K) : F :=
  evals.helpers k * (∏ i ∈ groups k, termPhiAtPoint xChallenge evals i) -
    ∑ i ∈ groups k,
      termNumeratorAtPoint evals i *
        ∏ j ∈ (groups k).erase i, termPhiAtPoint xChallenge evals j

/-- The verifier's final check value `Q(eq(r,z), m(r), φᵢ(r), hₖ(r))` from paper (19). -/
noncomputable def qAtPoint (groups : PartialSumGroups M K) (xChallenge : F)
    (zChallenge rChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (evals : PointEvaluations F M K) : F :=
  ∑ k : Fin K, (
    evals.helpers k +
      MvPolynomial.eval rChallenge (MvPolynomial.eqPolynomial zChallenge) * batchingScalars k *
        domainIdentityAtPoint groups xChallenge evals k)

end QEvaluation

section SumcheckPolynomial

variable (F : Type) [Field F] (n M : ℕ)
variable (params : ProtocolParams M)

private theorem oraclePolynomial_eval_hypercube
    (oracle : MultilinearOracle F n) (u : (Fin n → Fin 2)) :
    MvPolynomial.eval (u : Fin n → F) (MvPolynomial.MLE oracle.values)
      = oracle u := by
  simp

private noncomputable def inputOraclePolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (idx : InputOracleIdx M) :
    MvPolynomial (Fin n) F :=
  match idx with
  | .table => MvPolynomial.MLE (oStmt (.input .table)).values
  | .column i => MvPolynomial.MLE (oStmt (.input (.column i))).values

private noncomputable def multiplicityPolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.MLE (oStmt .multiplicity).values

private noncomputable def helperPolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.MLE ((oStmt .helpers) k).values

private noncomputable def termPhiPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : TermIdx M) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C stmt.xChallenge + inputOraclePolynomial F n M params oStmt (termToInput i)

private noncomputable def termNumeratorPolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : TermIdx M) :
    MvPolynomial (Fin n) F :=
  match termToInput i with
  | .table => multiplicityPolynomial F n M params oStmt
  | .column _ => MvPolynomial.C (-1)

private noncomputable def domainIdentityPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups) :
    MvPolynomial (Fin n) F :=
  helperPolynomial F n M params oStmt k *
      (∏ i ∈ canonicalGroups params k, termPhiPolynomial F n M params stmt oStmt i) -
    ∑ i ∈ canonicalGroups params k,
      termNumeratorPolynomial F n M params oStmt i *
        ∏ j ∈ (canonicalGroups params k).erase i,
          termPhiPolynomial F n M params stmt oStmt j

private theorem inputOraclePolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (idx : InputOracleIdx M)
    (i : Fin n) :
    MvPolynomial.degreeOf i (inputOraclePolynomial F n M params oStmt idx) ≤ 1 := by
  cases idx with
  | table =>
      simpa [inputOraclePolynomial] using
        (MvPolynomial.MLE_degreeOf (R := F) ((oStmt (.input .table)).values) i)
  | column j =>
      simpa [inputOraclePolynomial] using
        (MvPolynomial.MLE_degreeOf (R := F) ((oStmt (.input (.column j))).values) i)

private theorem multiplicityPolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : Fin n) :
    MvPolynomial.degreeOf i (multiplicityPolynomial F n M params oStmt) ≤ 1 := by
  simpa [multiplicityPolynomial] using
    (MvPolynomial.MLE_degreeOf (R := F) ((oStmt .multiplicity).values) i)

private theorem helperPolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups)
    (i : Fin n) :
    MvPolynomial.degreeOf i (helperPolynomial F n M params oStmt k) ≤ 1 := by
  simpa [helperPolynomial] using
    (MvPolynomial.MLE_degreeOf (R := F) (((oStmt .helpers) k).values) i)

private theorem termPhiPolynomial_degreeOf
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (j : TermIdx M) (i : Fin n) :
    MvPolynomial.degreeOf i (termPhiPolynomial F n M params stmt oStmt j) ≤ 1 := by
  calc
    _ ≤ max (MvPolynomial.degreeOf i (MvPolynomial.C stmt.xChallenge))
        (MvPolynomial.degreeOf i (inputOraclePolynomial F n M params oStmt (termToInput j))) := by
      exact MvPolynomial.degreeOf_add_le i _ _
    _ ≤ max 0 1 := by
      gcongr
      · exact (MvPolynomial.degreeOf_C (R := F) stmt.xChallenge i).le
      · exact inputOraclePolynomial_degreeOf F n M params oStmt (termToInput j) i
    _ = 1 := by
      omega

private theorem termNumeratorPolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (j : TermIdx M) (i : Fin n) :
    MvPolynomial.degreeOf i (termNumeratorPolynomial F n M params oStmt j) ≤ 1 := by
  unfold termNumeratorPolynomial
  cases h : termToInput j with
  | table =>
      simpa [h, multiplicityPolynomial] using
        multiplicityPolynomial_degreeOf F n M params oStmt i
  | column c =>
      exact (MvPolynomial.degreeOf_C (R := F) (-1 : F) i).le.trans (by omega)

private theorem finset_card_termIdx_le (s : Finset (TermIdx M)) :
    s.card ≤ M + 1 := by
  simpa [TermIdx] using Finset.card_le_univ (s := s)

private theorem termPhiPolynomial_prod_degreeOf
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (s : Finset (TermIdx M))
    (i : Fin n) :
    MvPolynomial.degreeOf i
        (∏ j ∈ s, termPhiPolynomial F n M params stmt oStmt j) ≤ M + 1 := by
  calc
    _ ≤ ∑ j ∈ s,
        MvPolynomial.degreeOf i (termPhiPolynomial F n M params stmt oStmt j) := by
      exact MvPolynomial.degreeOf_prod_le i _ _
    _ ≤ ∑ _j ∈ s, 1 := by
      apply Finset.sum_le_sum
      intro j _
      exact termPhiPolynomial_degreeOf F n M params stmt oStmt j i
    _ = s.card := by
      simp
    _ ≤ M + 1 := finset_card_termIdx_le M s

private theorem domainIdentityPolynomial_degreeOf
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups)
    (i : Fin n) :
    MvPolynomial.degreeOf i (domainIdentityPolynomial F n M params stmt oStmt k) ≤ M + 2 := by
  unfold domainIdentityPolynomial
  have hProd :
      MvPolynomial.degreeOf i
        (∏ j ∈ canonicalGroups params k, termPhiPolynomial F n M params stmt oStmt j) ≤
          M + 1 :=
    termPhiPolynomial_prod_degreeOf F n M params stmt oStmt (canonicalGroups params k) i
  have hLeft :
      MvPolynomial.degreeOf i
        (helperPolynomial F n M params oStmt k *
          (∏ j ∈ canonicalGroups params k, termPhiPolynomial F n M params stmt oStmt j)) ≤
        M + 2 := by
    calc
      _ ≤ MvPolynomial.degreeOf i (helperPolynomial F n M params oStmt k) +
          MvPolynomial.degreeOf i
            (∏ j ∈ canonicalGroups params k,
              termPhiPolynomial F n M params stmt oStmt j) := by
        exact MvPolynomial.degreeOf_mul_le i _ _
      _ ≤ 1 + (M + 1) := by
        gcongr
        exact helperPolynomial_degreeOf F n M params oStmt k i
      _ = M + 2 := by
        omega
  have hRight :
      MvPolynomial.degreeOf i
        (∑ j ∈ canonicalGroups params k,
          termNumeratorPolynomial F n M params oStmt j *
            ∏ l ∈ (canonicalGroups params k).erase j,
              termPhiPolynomial F n M params stmt oStmt l) ≤
        M + 2 := by
    calc
      _ ≤ (canonicalGroups params k).sup fun j =>
          MvPolynomial.degreeOf i
            (termNumeratorPolynomial F n M params oStmt j *
              ∏ l ∈ (canonicalGroups params k).erase j,
                termPhiPolynomial F n M params stmt oStmt l) := by
        exact MvPolynomial.degreeOf_sum_le i _ _
      _ ≤ M + 2 := by
        apply Finset.sup_le
        intro j _
        have hEraseProd :
            MvPolynomial.degreeOf i
              (∏ l ∈ (canonicalGroups params k).erase j,
                termPhiPolynomial F n M params stmt oStmt l) ≤ M + 1 :=
          termPhiPolynomial_prod_degreeOf F n M params stmt oStmt
            ((canonicalGroups params k).erase j) i
        calc
          _ ≤ MvPolynomial.degreeOf i (termNumeratorPolynomial F n M params oStmt j) +
              MvPolynomial.degreeOf i
                (∏ l ∈ (canonicalGroups params k).erase j,
                  termPhiPolynomial F n M params stmt oStmt l) := by
            exact MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ 1 + (M + 1) := by
            gcongr
            exact termNumeratorPolynomial_degreeOf F n M params oStmt j i
          _ = M + 2 := by
            omega
  exact (MvPolynomial.degreeOf_sub_le i _ _).trans (max_le hLeft hRight)

/-- The concrete multivariate LogUp sumcheck polynomial before packaging with its degree proof. -/
noncomputable def logupQPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    MvPolynomial (Fin n) F :=
  ∑ k : Fin params.numGroups, (
    helperPolynomial F n M params oStmt k +
      MvPolynomial.eqPolynomial stmt.zChallenge *
        MvPolynomial.C (stmt.batchingScalars k) *
          domainIdentityPolynomial F n M params stmt oStmt k)

theorem logupQPolynomial_degreeOf
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : Fin n) :
    MvPolynomial.degreeOf i (logupQPolynomial F n M params stmt oStmt) ≤ M + 3 := by
  classical
  unfold logupQPolynomial
  calc
    _ ≤ (Finset.univ : Finset (Fin params.numGroups)).sup fun k =>
        MvPolynomial.degreeOf i
          (helperPolynomial F n M params oStmt k +
            MvPolynomial.eqPolynomial stmt.zChallenge *
              MvPolynomial.C (stmt.batchingScalars k) *
                domainIdentityPolynomial F n M params stmt oStmt k) := by
      exact MvPolynomial.degreeOf_sum_le i _ _
    _ ≤ M + 3 := by
      apply Finset.sup_le
      intro k _
      have hHelper : MvPolynomial.degreeOf i (helperPolynomial F n M params oStmt k) ≤ M + 3 :=
        (helperPolynomial_degreeOf F n M params oStmt k i).trans (by omega)
      have hProduct :
          MvPolynomial.degreeOf i
            (MvPolynomial.eqPolynomial stmt.zChallenge *
              MvPolynomial.C (stmt.batchingScalars k) *
                domainIdentityPolynomial F n M params stmt oStmt k) ≤ M + 3 := by
        calc
          _ ≤ MvPolynomial.degreeOf i
                (MvPolynomial.eqPolynomial stmt.zChallenge *
                  MvPolynomial.C (stmt.batchingScalars k)) +
              MvPolynomial.degreeOf i
                (domainIdentityPolynomial F n M params stmt oStmt k) := by
            exact MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ (MvPolynomial.degreeOf i (MvPolynomial.eqPolynomial stmt.zChallenge) +
                MvPolynomial.degreeOf i (MvPolynomial.C (stmt.batchingScalars k))) +
              MvPolynomial.degreeOf i
                (domainIdentityPolynomial F n M params stmt oStmt k) := by
            gcongr
            exact MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ (1 + 0) + (M + 2) := by
            gcongr
            · exact MvPolynomial.eqPolynomial_degreeOf (R := F) stmt.zChallenge i
            · exact (MvPolynomial.degreeOf_C (R := F) (stmt.batchingScalars k) i).le
            · exact domainIdentityPolynomial_degreeOf F n M params stmt oStmt k i
          _ = M + 3 := by
            omega
      exact (MvPolynomial.degreeOf_add_le i _ _).trans (max_le hHelper hProduct)

private theorem termPhiPolynomial_eval_hypercube
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (i : TermIdx M) (u : (Fin n → Fin 2)) :
    MvPolynomial.eval (u : Fin n → F) (termPhiPolynomial F n M params stmt oStmt i)
      = termPhi (fun idx => oStmt (.input idx)) stmt.xChallenge i u := by
  rcases h : termToInput i with _ | c <;>
    simp only [termPhiPolynomial, termPhi, phi, h, inputOraclePolynomial, tableOracle,
      columnOracle, map_add, MvPolynomial.eval_C, oraclePolynomial_eval_hypercube F n]

private theorem termNumeratorPolynomial_eval_hypercube
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : TermIdx M) (u : (Fin n → Fin 2)) :
    MvPolynomial.eval (u : Fin n → F) (termNumeratorPolynomial F n M params oStmt i)
      = termNumerator (oStmt .multiplicity) i u := by
  unfold termNumeratorPolynomial termNumerator numerator
  cases termToInput i with
  | table => simp only [multiplicityPolynomial, oraclePolynomial_eval_hypercube F n]
  | column c => simp

private theorem domainIdentityPolynomial_eval_hypercube
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (k : Fin params.numGroups) (u : (Fin n → Fin 2)) :
    MvPolynomial.eval (u : Fin n → F) (domainIdentityPolynomial F n M params stmt oStmt k)
      = domainIdentityTerm (canonicalGroups params) (fun idx => oStmt (.input idx))
          (oStmt .multiplicity) (oStmt .helpers) stmt.xChallenge k u := by
  rw [domainIdentityPolynomial, map_sub, map_mul, map_prod, domainIdentityTerm,
    denominatorProduct, map_sum]
  congr 1
  · congr 1
    · simp only [helperPolynomial]; exact oraclePolynomial_eval_hypercube F n _ u
    · exact Finset.prod_congr rfl
        (fun i _ => termPhiPolynomial_eval_hypercube F n M params stmt oStmt i u)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_prod, termNumeratorPolynomial_eval_hypercube F n M params]
    congr 1
    exact Finset.prod_congr rfl
      (fun j _ => termPhiPolynomial_eval_hypercube F n M params stmt oStmt j u)

/-- Denominator polynomials evaluated at an arbitrary point match the reconstructed final-query
denominators. -/
private theorem termPhiPolynomial_eval_point
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (hEval : logupPointEvaluationsAgree (F := F) (n := n) (M := M) params r oStmt evals)
    (i : TermIdx M) :
    MvPolynomial.eval r (termPhiPolynomial F n M params stmt oStmt i)
      = termPhiAtPoint stmt.xChallenge evals i := by
  rcases h : termToInput i with _ | c
  · simp only [termPhiPolynomial, termPhiAtPoint, phiAtPoint, h, inputOraclePolynomial,
      map_add, MvPolynomial.eval_C]
    exact congrArg (fun y => stmt.xChallenge + y) hEval.2.1.symm
  · simp only [termPhiPolynomial, termPhiAtPoint, phiAtPoint, h, inputOraclePolynomial,
      map_add, MvPolynomial.eval_C]
    exact congrArg (fun y => stmt.xChallenge + y) (hEval.2.2.1 c).symm

/-- Numerator polynomials evaluated at an arbitrary point match the reconstructed final-query
numerators. -/
private theorem termNumeratorPolynomial_eval_point
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (hEval : logupPointEvaluationsAgree (F := F) (n := n) (M := M) params r oStmt evals)
    (i : TermIdx M) :
    MvPolynomial.eval r (termNumeratorPolynomial F n M params oStmt i)
      = termNumeratorAtPoint evals i := by
  unfold termNumeratorPolynomial termNumeratorAtPoint numeratorAtPoint
  cases h : termToInput i with
  | table =>
      simp only [multiplicityPolynomial]
      exact hEval.1.symm
  | column c =>
      simp

/-- The cleared-denominator identity polynomial evaluated at the final point matches the
reconstructed final-query expression. -/
private theorem domainIdentityPolynomial_eval_point
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (hEval : logupPointEvaluationsAgree (F := F) (n := n) (M := M) params r oStmt evals)
    (k : Fin params.numGroups) :
    MvPolynomial.eval r (domainIdentityPolynomial F n M params stmt oStmt k)
      = domainIdentityAtPoint (canonicalGroups params) stmt.xChallenge evals k := by
  rw [domainIdentityPolynomial, domainIdentityAtPoint, map_sub, map_mul, map_prod, map_sum]
  congr 1
  · congr 1
    · simp only [helperPolynomial]
      exact (hEval.2.2.2 k).symm
    · exact Finset.prod_congr rfl
        (fun i _ => termPhiPolynomial_eval_point F n M params stmt oStmt r evals hEval i)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_prod, termNumeratorPolynomial_eval_point F n M params oStmt r evals hEval]
    congr 1
    exact Finset.prod_congr rfl
      (fun j _ => termPhiPolynomial_eval_point F n M params stmt oStmt r evals hEval j)

/-- `logupQPolynomial` restricted to the Boolean hypercube agrees with `qOnHypercube`. -/
theorem logupQPolynomial_eval_hypercube
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (u : (Fin n → Fin 2)) :
    MvPolynomial.eval (u : Fin n → F) (logupQPolynomial F n M params stmt oStmt)
      = qOnHypercube (canonicalGroups params) (fun i => oStmt (.input i)) (oStmt .multiplicity)
          (oStmt .helpers) stmt.xChallenge stmt.zChallenge stmt.batchingScalars u := by
  rw [logupQPolynomial, qOnHypercube, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_add, map_mul, map_mul, MvPolynomial.eval_C,
    show MvPolynomial.eval (u : Fin n → F) (helperPolynomial F n M params oStmt k)
        = ((oStmt .helpers) k) u from by
      simp only [helperPolynomial]; exact oraclePolynomial_eval_hypercube F n _ u,
    domainIdentityPolynomial_eval_hypercube F n M params]

/-- `logupQPolynomial` evaluated at the sumcheck point agrees with the value reconstructed from
the final LogUp oracle-query answers. -/
theorem logupQPolynomial_eval_point
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (hEval : logupPointEvaluationsAgree (F := F) (n := n) (M := M) params r oStmt evals) :
    MvPolynomial.eval r (logupQPolynomial F n M params stmt oStmt)
      = qAtPoint (canonicalGroups params) stmt.xChallenge stmt.zChallenge r
          stmt.batchingScalars evals := by
  rw [logupQPolynomial, qAtPoint, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_add, map_mul, map_mul, MvPolynomial.eval_C,
    show MvPolynomial.eval r (helperPolynomial F n M params oStmt k) = evals.helpers k from by
      simp only [helperPolynomial]
      exact (hEval.2.2.2 k).symm,
    domainIdentityPolynomial_eval_point F n M params stmt oStmt r evals hEval]

end SumcheckPolynomial

end Logup

import ArkLib.Data.MvPolynomial.Degrees
import ArkLib.ProofSystem.Logup.Common

/-!
# LogUp Sumcheck Polynomial

Construction of the concrete polynomial used by LogUp's embedded sumcheck, following Protocol 2 of
Haböck's LogUp paper (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

The outer LogUp algebra defines a row-wise expression `qOnHypercube`. This file builds its
multilinear-extension-style polynomial `logupQPolynomial : MvPolynomial (Fin n) F`, proves that it
agrees with `qOnHypercube` on the signed hypercube, and proves the individual-degree bound
`degreeOf ≤ M + 3` needed by the generic sumcheck.
-/

namespace Logup

open scoped BigOperators

section SumcheckPolynomial

variable (F : Type) [Field F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The `{±1}` Lagrange basis polynomial for one hypercube row. -/
private noncomputable def signedBasisPolynomial (u : Hypercube n) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C (((2 : F) ^ n)⁻¹) *
    ∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)

/-- Multilinear extension of a function on the signed hypercube `{±1}ⁿ`. -/
private noncomputable def signedMLEPolynomial (values : Hypercube n → F) :
    MvPolynomial (Fin n) F :=
  ∑ u : Hypercube n, MvPolynomial.C (values u) * signedBasisPolynomial F n u

/-- The polynomial whose value at `r` is `L_H(r, z)`. -/
private noncomputable def lagrangeKernelPolynomial (z : Fin n → F) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C (((2 : F) ^ n)⁻¹) *
    ∏ j : Fin n, (1 + MvPolynomial.C (z j) * MvPolynomial.X j)

private theorem signedBasisPolynomial_eval (u : Hypercube n) (r : Fin n → F) :
    MvPolynomial.eval r (signedBasisPolynomial F n u) = lagrangeKernel F u r := by
  simp [signedBasisPolynomial, lagrangeKernel, lagrangeKernelAtPoint, signPoint]

private theorem signedMLEPolynomial_eval (values : Hypercube n → F) (r : Fin n → F) :
    MvPolynomial.eval r (signedMLEPolynomial F n values) =
      ∑ u : Hypercube n, values u * lagrangeKernel F u r := by
  simp [signedMLEPolynomial, signedBasisPolynomial_eval]

private theorem lagrangeKernelPolynomial_eval (z r : Fin n → F) :
    MvPolynomial.eval r (lagrangeKernelPolynomial F n z) =
      lagrangeKernelAtPoint F r z := by
  simp [lagrangeKernelPolynomial, lagrangeKernelAtPoint, mul_comm]

private theorem signedLinearFactor_degreeOf (a : F) (i j : Fin n) :
    MvPolynomial.degreeOf i (1 + MvPolynomial.C a * MvPolynomial.X j) ≤
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst i
    simp only [↓reduceIte]
    have hone :
        MvPolynomial.degreeOf j (1 : MvPolynomial (Fin n) F) ≤ 1 := by
      simp
    have hmul :
        MvPolynomial.degreeOf j (MvPolynomial.C a * MvPolynomial.X j) ≤ 1 := by
      calc
        _ ≤ MvPolynomial.degreeOf j (MvPolynomial.C a) +
            MvPolynomial.degreeOf j (MvPolynomial.X j) := by
          exact MvPolynomial.degreeOf_mul_le j _ _
        _ ≤ 0 + 1 := by
          gcongr
          · exact (MvPolynomial.degreeOf_C (R := F) a j).le
          · exact MvPolynomial.degreeOf_X_le (R := F) j j
        _ = 1 := by omega
    exact (MvPolynomial.degreeOf_add_le j _ _).trans (max_le hone hmul)
  · simp only [hij, ↓reduceIte]
    have hone :
        MvPolynomial.degreeOf i (1 : MvPolynomial (Fin n) F) ≤ 0 := by
      simp
    have hmul :
        MvPolynomial.degreeOf i (MvPolynomial.C a * MvPolynomial.X j) ≤ 0 := by
      calc
        _ ≤ MvPolynomial.degreeOf i (MvPolynomial.C a) +
            MvPolynomial.degreeOf i (MvPolynomial.X j) := by
          exact MvPolynomial.degreeOf_mul_le i _ _
        _ ≤ 0 + 0 := by
          gcongr
          · exact (MvPolynomial.degreeOf_C (R := F) a i).le
          · exact (MvPolynomial.degreeOf_X_of_ne (R := F) hij).le
        _ = 0 := by omega
    exact (MvPolynomial.degreeOf_add_le i _ _).trans (max_le hone hmul)

private theorem signedBasisPolynomial_degreeOf (u : Hypercube n) (i : Fin n) :
    MvPolynomial.degreeOf i (signedBasisPolynomial F n u) ≤ 1 := by
  calc
    _ ≤ MvPolynomial.degreeOf i (MvPolynomial.C (((2 : F) ^ n)⁻¹)) +
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)) := by
      exact MvPolynomial.degreeOf_mul_le i _ _
    _ ≤ 0 +
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)) := by
      gcongr
      exact (MvPolynomial.degreeOf_C (R := F) (((2 : F) ^ n)⁻¹) i).le
    _ =
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)) := by
      simp
    _ ≤ ∑ j : Fin n,
        MvPolynomial.degreeOf i (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j) := by
      exact MvPolynomial.degreeOf_prod_le i _ _
    _ ≤ ∑ j : Fin n, if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      exact signedLinearFactor_degreeOf F n (bitToSign F (u j)) i j
    _ = 1 := by
      norm_num

private theorem signedMLEPolynomial_degreeOf (values : Hypercube n → F) (i : Fin n) :
    MvPolynomial.degreeOf i (signedMLEPolynomial F n values) ≤ 1 := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Hypercube n)).sup
        fun u => MvPolynomial.degreeOf i
          (MvPolynomial.C (values u) * signedBasisPolynomial F n u) := by
      exact MvPolynomial.degreeOf_sum_le i _ _
    _ ≤ 1 := by
      apply Finset.sup_le
      intro u _
      calc
        MvPolynomial.degreeOf i (MvPolynomial.C (values u) * signedBasisPolynomial F n u)
            ≤ MvPolynomial.degreeOf i (MvPolynomial.C (values u)) +
              MvPolynomial.degreeOf i (signedBasisPolynomial F n u) := by
          exact MvPolynomial.degreeOf_mul_le i _ _
        _ ≤ 0 + 1 := by
          gcongr
          · exact (MvPolynomial.degreeOf_C (R := F) (values u) i).le
          · exact signedBasisPolynomial_degreeOf F n u i
        _ = 1 := by omega

private theorem lagrangeKernelPolynomial_degreeOf (z : Fin n → F) (i : Fin n) :
    MvPolynomial.degreeOf i (lagrangeKernelPolynomial F n z) ≤ 1 := by
  calc
    _ ≤ MvPolynomial.degreeOf i (MvPolynomial.C (((2 : F) ^ n)⁻¹)) +
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (z j) * MvPolynomial.X j)) := by
      exact MvPolynomial.degreeOf_mul_le i _ _
    _ ≤ 0 +
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (z j) * MvPolynomial.X j)) := by
      gcongr
      exact (MvPolynomial.degreeOf_C (R := F) (((2 : F) ^ n)⁻¹) i).le
    _ =
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (z j) * MvPolynomial.X j)) := by
      simp
    _ ≤ ∑ j : Fin n,
        MvPolynomial.degreeOf i (1 + MvPolynomial.C (z j) * MvPolynomial.X j) := by
      exact MvPolynomial.degreeOf_prod_le i _ _
    _ ≤ ∑ j : Fin n, if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      exact signedLinearFactor_degreeOf F n (z j) i j
    _ = 1 := by
      norm_num

/-- Polynomial extension of one retained Lagrange-form multilinear oracle. -/
private noncomputable def multilinearOraclePolynomial (oracle : MultilinearOracle F n) :
    MvPolynomial (Fin n) F :=
  signedMLEPolynomial F n fun u => evalOnHypercube oracle u

private theorem multilinearOraclePolynomial_eval (oracle : MultilinearOracle F n)
    (r : Fin n → F) :
    MvPolynomial.eval r (multilinearOraclePolynomial F n oracle) =
      lagrangeOracleEval oracle r := by
  simp [multilinearOraclePolynomial, signedMLEPolynomial_eval, lagrangeOracleEval,
    evalOnHypercube]

/-- On the signed hypercube the Lagrange kernel is a delta function. -/
theorem lagrangeKernel_signPoint (hs : (-1 : F) ≠ 1) (v u : Hypercube n) :
    lagrangeKernel F v (signPoint F u) = if v = u then 1 else 0 := by
  have h2 : (2 : F) ≠ 0 := fun h => hs (by linear_combination -h)
  unfold lagrangeKernel lagrangeKernelAtPoint
  by_cases h : v = u
  · subst h
    rw [if_pos rfl]
    have hfac : ∀ j, 1 + signPoint F v j * signPoint F v j = (2 : F) := by
      intro j
      show (1 : F) + bitToSign F (v j) * bitToSign F (v j) = 2
      generalize v j = b
      fin_cases b <;> norm_num [bitToSign]
    rw [Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, inv_mul_cancel₀ (pow_ne_zero n h2)]
  · rw [if_neg h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    have hfac : 1 + signPoint F v j * signPoint F u j = 0 := by
      show (1 : F) + bitToSign F (v j) * bitToSign F (u j) = 0
      generalize hvj : v j = b at hj
      generalize huj : u j = c at hj
      fin_cases b <;> fin_cases c <;> simp_all [bitToSign]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hfac, mul_zero]

/-- The MLE of an oracle, evaluated at a signed-hypercube point, recovers the oracle's value. -/
theorem lagrangeOracleEval_signPoint (hs : (-1 : F) ≠ 1)
    (oracle : MultilinearOracle F n) (u : Hypercube n) :
    lagrangeOracleEval oracle (signPoint F u) = evalOnHypercube oracle u := by
  unfold lagrangeOracleEval
  rw [Finset.sum_congr rfl (fun v _ => by rw [lagrangeKernel_signPoint F n hs v u])]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    evalOnHypercube]

private theorem multilinearOraclePolynomial_eval_sign (hs : (-1 : F) ≠ 1)
    (oracle : MultilinearOracle F n) (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (multilinearOraclePolynomial F n oracle)
      = evalOnHypercube oracle u := by
  rw [multilinearOraclePolynomial_eval, lagrangeOracleEval_signPoint F n hs]

private noncomputable def inputOraclePolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (idx : InputOracleIdx M) :
    MvPolynomial (Fin n) F :=
  match idx with
  | .table => multilinearOraclePolynomial F n (oStmt (.input .table))
  | .column i => multilinearOraclePolynomial F n (oStmt (.input (.column i)))

private noncomputable def multiplicityPolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    MvPolynomial (Fin n) F :=
  multilinearOraclePolynomial F n (oStmt .multiplicity)

private noncomputable def helperPolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups) :
    MvPolynomial (Fin n) F :=
  multilinearOraclePolynomial F n ((oStmt .helpers) k)

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

private theorem multilinearOraclePolynomial_degreeOf (oracle : MultilinearOracle F n)
    (i : Fin n) :
    MvPolynomial.degreeOf i (multilinearOraclePolynomial F n oracle) ≤ 1 := by
  simpa [multilinearOraclePolynomial] using
    signedMLEPolynomial_degreeOf F n (fun u => evalOnHypercube oracle u) i

private theorem inputOraclePolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (idx : InputOracleIdx M)
    (i : Fin n) :
    MvPolynomial.degreeOf i (inputOraclePolynomial F n M params oStmt idx) ≤ 1 := by
  cases idx with
  | table =>
      simpa [inputOraclePolynomial] using
        multilinearOraclePolynomial_degreeOf F n (oStmt (.input .table)) i
  | column j =>
      simpa [inputOraclePolynomial] using
        multilinearOraclePolynomial_degreeOf F n (oStmt (.input (.column j))) i

private theorem multiplicityPolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : Fin n) :
    MvPolynomial.degreeOf i (multiplicityPolynomial F n M params oStmt) ≤ 1 :=
  multilinearOraclePolynomial_degreeOf F n (oStmt .multiplicity) i

private theorem helperPolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups)
    (i : Fin n) :
    MvPolynomial.degreeOf i (helperPolynomial F n M params oStmt k) ≤ 1 :=
  multilinearOraclePolynomial_degreeOf F n ((oStmt .helpers) k) i

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
      lagrangeKernelPolynomial F n stmt.zChallenge *
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
            lagrangeKernelPolynomial F n stmt.zChallenge *
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
            (lagrangeKernelPolynomial F n stmt.zChallenge *
              MvPolynomial.C (stmt.batchingScalars k) *
                domainIdentityPolynomial F n M params stmt oStmt k) ≤ M + 3 := by
        calc
          _ ≤ MvPolynomial.degreeOf i
                (lagrangeKernelPolynomial F n stmt.zChallenge *
                  MvPolynomial.C (stmt.batchingScalars k)) +
              MvPolynomial.degreeOf i
                (domainIdentityPolynomial F n M params stmt oStmt k) := by
            exact MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ (MvPolynomial.degreeOf i (lagrangeKernelPolynomial F n stmt.zChallenge) +
                MvPolynomial.degreeOf i (MvPolynomial.C (stmt.batchingScalars k))) +
              MvPolynomial.degreeOf i
                (domainIdentityPolynomial F n M params stmt oStmt k) := by
            gcongr
            exact MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ (1 + 0) + (M + 2) := by
            gcongr
            · exact lagrangeKernelPolynomial_degreeOf F n stmt.zChallenge i
            · exact (MvPolynomial.degreeOf_C (R := F) (stmt.batchingScalars k) i).le
            · exact domainIdentityPolynomial_degreeOf F n M params stmt oStmt k i
          _ = M + 3 := by
            omega
      exact (MvPolynomial.degreeOf_add_le i _ _).trans (max_le hHelper hProduct)

private theorem termPhiPolynomial_eval_sign (hs : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (i : TermIdx M) (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (termPhiPolynomial F n M params stmt oStmt i)
      = termPhi (fun idx => oStmt (.input idx)) stmt.xChallenge i u := by
  rcases h : termToInput i with _ | c <;>
    simp only [termPhiPolynomial, termPhi, phi, h, inputOraclePolynomial, tableOracle,
      columnOracle, map_add, MvPolynomial.eval_C, multilinearOraclePolynomial_eval_sign F n hs]

private theorem termNumeratorPolynomial_eval_sign (hs : (-1 : F) ≠ 1)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : TermIdx M) (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (termNumeratorPolynomial F n M params oStmt i)
      = termNumerator (oStmt .multiplicity) i u := by
  unfold termNumeratorPolynomial termNumerator numerator
  cases termToInput i with
  | table => simp only [multiplicityPolynomial, multilinearOraclePolynomial_eval_sign F n hs]
  | column c => simp

private theorem domainIdentityPolynomial_eval_sign (hs : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (k : Fin params.numGroups) (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (domainIdentityPolynomial F n M params stmt oStmt k)
      = domainIdentityTerm (canonicalGroups params) (fun idx => oStmt (.input idx))
          (oStmt .multiplicity) (oStmt .helpers) stmt.xChallenge k u := by
  rw [domainIdentityPolynomial, map_sub, map_mul, map_prod, domainIdentityTerm,
    denominatorProduct, map_sum]
  congr 1
  · congr 1
    · simp only [helperPolynomial]; exact multilinearOraclePolynomial_eval_sign F n hs _ u
    · exact Finset.prod_congr rfl
        (fun i _ => termPhiPolynomial_eval_sign F n M params hs stmt oStmt i u)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_prod, termNumeratorPolynomial_eval_sign F n M params hs]
    congr 1
    exact Finset.prod_congr rfl
      (fun j _ => termPhiPolynomial_eval_sign F n M params hs stmt oStmt j u)

/-- `logupQPolynomial` restricted to the signed hypercube agrees with `qOnHypercube`. -/
theorem logupQPolynomial_eval_signPoint (hs : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params) (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (logupQPolynomial F n M params stmt oStmt)
      = qOnHypercube (canonicalGroups params) (fun i => oStmt (.input i)) (oStmt .multiplicity)
          (oStmt .helpers) stmt.xChallenge stmt.zChallenge stmt.batchingScalars u := by
  rw [logupQPolynomial, qOnHypercube, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_add, map_mul, map_mul, MvPolynomial.eval_C,
    show MvPolynomial.eval (signPoint F u) (helperPolynomial F n M params oStmt k)
        = evalOnHypercube ((oStmt .helpers) k) u from by
      simp only [helperPolynomial]; exact multilinearOraclePolynomial_eval_sign F n hs _ u,
    show MvPolynomial.eval (signPoint F u) (lagrangeKernelPolynomial F n stmt.zChallenge)
        = lagrangeKernel F u stmt.zChallenge from by rw [lagrangeKernelPolynomial_eval]; rfl,
    domainIdentityPolynomial_eval_sign F n M params hs]

end SumcheckPolynomial

end Logup

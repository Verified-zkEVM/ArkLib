import ArkLib.OracleReduction.Security.Basic
import ArkLib.OracleReduction.Security.Implications
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import ArkLib.ProofSystem.Logup.Protocol
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec

/-!
# LogUp Soundness

Soundness target for the LogUp lookup argument (Cryptology ePrint Archive, Paper 2022/1530,
<https://eprint.iacr.org/2022/1530>).

The protocol verifier is the sequential composition of three phases (outer LogUp, embedded
sumcheck, final point check), so its soundness error decomposes as a sum of one error per phase.
We bound each phase separately and combine them with `OracleVerifier.append_soundness`, which
turns the soundness of a composed verifier into the sum of the parts' errors. This matches the
paper's Theorem 4, where the total error is `ε₁ + ε₂ + ε₃ + εsumcheck`.
-/

open scoped NNReal BigOperators

namespace Logup

section Soundness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-! ## Per-phase soundness errors

The three named errors below correspond to the failure events of the three protocol phases. Their
sum is the full LogUp soundness error `logupSoundnessError`. -/

/-- Soundness error of the outer LogUp reduction.

The reduction samples the challenge `x` that turns the rational lookup identity into a polynomial
identity of degree at most `|H| * (M + 1) - 1`, the Lagrange-kernel point `z` that must not hide a
nonzero multilinear domain identity, and the batching scalar that combines the `K + 1` zero-sum
claims into one.

The first two terms are an unconditional union bound over denominator poles and roots of the
cleared lookup identity. -/
noncomputable def logupOuterSoundnessError (F : Type) [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) : ℝ≥0 :=
  ((((M + 1) * Fintype.card (Fin n → Fin 2) : ℕ) : ℝ≥0) /
      (Fintype.card F : ℝ≥0)) +
    ((((M + 1) * Fintype.card (Fin n → Fin 2) - 1 : ℕ) : ℝ≥0) /
      (Fintype.card F : ℝ≥0)) +
    (((params.numGroups * n : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)) +
    ((1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- Soundness error of the final LogUp point check (paper's `ε₂ = K/|F|`).

This is the cost of reducing the domain identities to the Lagrange-kernel point evaluation, since
scalar products with the Lagrange kernel translate to point evaluation of the multilinear
extension. -/
noncomputable def logupFinalCheckSoundnessError (F : Type) [Fintype F] (M : ℕ)
    (params : ProtocolParams M) : ℝ≥0 :=
  ((params.numGroups : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- Full LogUp soundness error: the sum of the outer, embedded-sumcheck, and final-check errors.

The current formal outer phase uses the general Schwartz-Zippel bound for a nonzero multilinear
domain-identity MLE, so the outer contribution includes `K * n / |F|`. -/
noncomputable def logupSoundnessError (F : Type) [Fintype F] (n M : ℕ) (params : ProtocolParams M)
    (sumcheckSoundnessError : ℝ≥0) : ℝ≥0 :=
  logupOuterSoundnessError F n M params + sumcheckSoundnessError +
    logupFinalCheckSoundnessError F M params

/-- The generic Sumcheck soundness error used by LogUp's embedded sumcheck phase. -/
noncomputable def logupSumcheckSoundnessError (F : Type) [CommSemiring F] [Fintype F] (n M : ℕ)
    (params : ProtocolParams M) : ℝ≥0 :=
  ∑ _ : (Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n).ChallengeIdx,
    ((logupSumcheckDegree M params : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-! ## Local outer-soundness algebra

These are the missing algebraic ingredients for the outer phase. They live in this file for now so
the soundness proof has an explicit dependency graph; once the statements settle they can move to
`Algebra.lean` or a dedicated security-algebra file.
-/

/-- One occurrence in the common denominator of the LogUp rational identity: either a table row
or one lookup-column row. -/
inductive LookupOccur (n M : ℕ) where
  | table : (Fin n → Fin 2) → LookupOccur n M
  | column : Fin M → (Fin n → Fin 2) → LookupOccur n M
deriving DecidableEq, Fintype

/-- `LookupOccur` is table rows plus all column rows. -/
def LookupOccur.equivSum (n M : ℕ) :
    LookupOccur n M ≃ ((Fin n → Fin 2) ⊕ (Fin M × (Fin n → Fin 2))) where
  toFun
    | .table u => Sum.inl u
    | .column i u => Sum.inr (i, u)
  invFun
    | Sum.inl u => .table u
    | Sum.inr (i, u) => .column i u
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl u => rfl
    | inr iu =>
        rcases iu with ⟨i, u⟩
        rfl

/-- Cardinality of denominator occurrences in the cleared lookup identity. -/
theorem LookupOccur.card (n M : ℕ) :
    Fintype.card (LookupOccur n M) = (M + 1) * Fintype.card (Fin n → Fin 2) := by
  rw [Fintype.card_congr (LookupOccur.equivSum n M)]
  simp [Fintype.card_sum, Fintype.card_prod, Nat.succ_mul, Nat.add_comm]

/-- The field value attached to a denominator occurrence. -/
def lookupOccurValue {F : Type} {n M : ℕ}
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F) :
    LookupOccur n M → F
  | .table u => table u
  | .column i u => columns i u

/-- The numerator attached to a denominator occurrence: `m(u)` for table rows and `-1` for lookup
column rows. -/
def lookupOccurNumerator {F : Type} [Neg F] [One F] {n M : ℕ}
    (multiplicity : (Fin n → Fin 2) → F) : LookupOccur n M → F
  | .table u => multiplicity u
  | .column _ _ => -1

/-- The cleared univariate lookup identity obtained from paper equation (13) by multiplying by the
common denominator over all table and column occurrences. -/
noncomputable def clearedLookupIdentity {F : Type} [Field F] {n M : ℕ}
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) : Polynomial F :=
  ∑ a : LookupOccur n M,
    Polynomial.C (lookupOccurNumerator multiplicity a) *
      ∏ b ∈ (Finset.univ.erase a),
        (Polynomial.X + Polynomial.C (lookupOccurValue table columns b))

/-- A generic version of `clearedLookupIdentity`, indexed by arbitrary denominator occurrences. -/
noncomputable def clearedOccurrences {α : Type} [Fintype α] [DecidableEq α]
    (value coeff : α → F) : Polynomial F :=
  ∑ a : α,
    Polynomial.C (coeff a) *
      ∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (value b))

omit [Fintype F] [SampleableType F] in
/-- The key repeated-pole coefficient calculation. After shifting by a value `z`, the coefficient
of the first possible power of `X` in the cleared occurrence polynomial is the total coefficient
on the `z`-fiber, times the nonzero product of the other shifted values. -/
theorem clearedOccurrences_taylor_coeff_fiber_pred
    {α : Type} [Fintype α] [DecidableEq α]
    (value coeff : α → F) (z : F)
    (hfiber : 0 < (Finset.univ.filter fun a : α => value a = z).card) :
    (Polynomial.taylor (-z) (clearedOccurrences (F := F) value coeff)).coeff
        ((Finset.univ.filter fun a : α => value a = z).card - 1) =
      (∑ a ∈ (Finset.univ.filter fun a : α => value a = z), coeff a) *
        ∏ b ∈ (Finset.univ.filter fun b : α => value b ≠ z), (-z + value b) := by
  classical
  let fiber : Finset α := Finset.univ.filter fun a : α => value a = z
  let rest : Finset α := Finset.univ.filter fun b : α => value b ≠ z
  let shifted : α → F := fun b => -z + value b
  have hrest_coeff0 :
      (∏ b ∈ rest, (Polynomial.X + Polynomial.C (shifted b))).coeff 0 =
        ∏ b ∈ rest, shifted b := by
    simp [Polynomial.coeff_zero_prod, shifted]
  have hterm :
      ∀ a : α,
        (Polynomial.taylor (-z)
            (Polynomial.C (coeff a) *
              ∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (value b)))).coeff
            (fiber.card - 1) =
          if value a = z then coeff a * ∏ b ∈ rest, shifted b else 0 := by
    intro a
    have htaylor :
        Polynomial.taylor (-z)
            (Polynomial.C (coeff a) *
              ∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (value b))) =
          Polynomial.C (coeff a) *
            ∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (shifted b)) := by
      change Polynomial.taylorAlgHom (-z)
            (Polynomial.C (coeff a) *
              ∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (value b))) =
          Polynomial.C (coeff a) *
            ∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (shifted b))
      rw [map_mul, map_prod]
      simp [Polynomial.taylorAlgHom, shifted, add_assoc]
    by_cases ha : value a = z
    · have hafiber : a ∈ fiber := by simp [fiber, ha]
      have hfiberErase :
          (Finset.univ.erase a).filter (fun b : α => value b = z) = fiber.erase a := by
        simp [fiber, Finset.filter_erase]
      have hrestErase :
          (Finset.univ.erase a).filter (fun b : α => value b ≠ z) = rest := by
        ext b
        by_cases hba : b = a <;> simp [rest, hba, ha]
      have hsplit :
          (∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (shifted b))) =
            Polynomial.X ^ (fiber.card - 1) *
              ∏ b ∈ rest, (Polynomial.X + Polynomial.C (shifted b)) := by
        calc
          (∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (shifted b)))
              =
              (∏ b ∈ (Finset.univ.erase a).filter (fun b : α => value b = z),
                (Polynomial.X + Polynomial.C (shifted b))) *
                ∏ b ∈ (Finset.univ.erase a).filter (fun b : α => value b ≠ z),
                  (Polynomial.X + Polynomial.C (shifted b)) := by
                rw [← Finset.prod_filter_mul_prod_filter_not
                  (p := fun b : α => value b = z)]
          _ =
              (∏ _b ∈ fiber.erase a, (Polynomial.X : Polynomial F)) *
                ∏ b ∈ rest, (Polynomial.X + Polynomial.C (shifted b)) := by
                rw [hfiberErase, hrestErase]
                congr 1
                refine Finset.prod_congr rfl ?_
                intro b hb
                simp [fiber, shifted] at hb ⊢
                simp [hb.2]
          _ =
              Polynomial.X ^ (fiber.card - 1) *
                ∏ b ∈ rest, (Polynomial.X + Polynomial.C (shifted b)) := by
                simp [Finset.prod_const, Finset.card_erase_of_mem hafiber]
      rw [htaylor, hsplit, Polynomial.coeff_C_mul]
      have hcoeffX :
          (Polynomial.X ^ (fiber.card - 1) *
            ∏ b ∈ rest, (Polynomial.X + Polynomial.C (shifted b))).coeff
              (fiber.card - 1) =
            (∏ b ∈ rest, (Polynomial.X + Polynomial.C (shifted b))).coeff 0 := by
        simpa using
          (Polynomial.coeff_X_pow_mul
            (∏ b ∈ rest, (Polynomial.X + Polynomial.C (shifted b)))
            (fiber.card - 1) 0)
      rw [hcoeffX, hrest_coeff0]
      simp [ha]
    · have hfiberErase :
          (Finset.univ.erase a).filter (fun b : α => value b = z) = fiber := by
        ext b
        by_cases hba : b = a <;> simp [fiber, hba, ha]
      have hsplit :
          (∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (shifted b))) =
            Polynomial.X ^ fiber.card *
              ∏ b ∈ (Finset.univ.erase a).filter (fun b : α => value b ≠ z),
                (Polynomial.X + Polynomial.C (shifted b)) := by
        calc
          (∏ b ∈ (Finset.univ.erase a), (Polynomial.X + Polynomial.C (shifted b)))
              =
              (∏ b ∈ (Finset.univ.erase a).filter (fun b : α => value b = z),
                (Polynomial.X + Polynomial.C (shifted b))) *
                ∏ b ∈ (Finset.univ.erase a).filter (fun b : α => value b ≠ z),
                  (Polynomial.X + Polynomial.C (shifted b)) := by
                rw [← Finset.prod_filter_mul_prod_filter_not
                  (p := fun b : α => value b = z)]
          _ =
              (∏ _b ∈ fiber, (Polynomial.X : Polynomial F)) *
                ∏ b ∈ (Finset.univ.erase a).filter (fun b : α => value b ≠ z),
                  (Polynomial.X + Polynomial.C (shifted b)) := by
                rw [hfiberErase]
                congr 1
                refine Finset.prod_congr rfl ?_
                intro b hb
                simp [fiber, shifted] at hb ⊢
                simp [hb]
          _ =
              Polynomial.X ^ fiber.card *
                ∏ b ∈ (Finset.univ.erase a).filter (fun b : α => value b ≠ z),
                  (Polynomial.X + Polynomial.C (shifted b)) := by
                simp [Finset.prod_const]
      rw [htaylor, hsplit, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
      have hfiber' : 0 < fiber.card := by
        simpa [fiber] using hfiber
      have hnot : ¬ fiber.card ≤ fiber.card - 1 :=
        Nat.not_le.mpr (Nat.pred_lt (Nat.ne_of_gt hfiber'))
      simp [ha, hnot]
  unfold clearedOccurrences
  change
    (Polynomial.taylor (-z)
      (∑ a : α,
        Polynomial.C (coeff a) *
          ∏ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C (value b)))).coeff
        (fiber.card - 1) =
      (∑ a ∈ fiber, coeff a) * ∏ b ∈ rest, shifted b
  rw [map_sum, Polynomial.finsetSum_coeff]
  calc
    ∑ a : α,
        (Polynomial.taylor (-z)
          (Polynomial.C (coeff a) *
            ∏ b ∈ Finset.univ.erase a, (Polynomial.X + Polynomial.C (value b)))).coeff
          (fiber.card - 1)
        = ∑ a : α, if value a = z then coeff a * ∏ b ∈ rest, shifted b else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact hterm a
    _ = ∑ a ∈ fiber, coeff a * ∏ b ∈ rest, shifted b := by
          simp [fiber, Finset.sum_filter]
    _ = (∑ a ∈ fiber, coeff a) * ∏ b ∈ rest, shifted b := by
          rw [Finset.sum_mul]

omit [Fintype F] [SampleableType F] in
/-- If the total coefficient on one denominator-value fiber is nonzero, then the cleared
occurrence polynomial cannot vanish, even when the denominator value occurs repeatedly. -/
theorem clearedOccurrences_ne_zero_of_fiber_sum_ne_zero
    {α : Type} [Fintype α] [DecidableEq α]
    (value coeff : α → F) {z : F}
    (hfiber : 0 < (Finset.univ.filter fun a : α => value a = z).card)
    (hsum : (∑ a ∈ (Finset.univ.filter fun a : α => value a = z), coeff a) ≠ 0) :
    clearedOccurrences (F := F) value coeff ≠ 0 := by
  classical
  intro hzero
  have hcoeff_zero :
      (Polynomial.taylor (-z) (clearedOccurrences (F := F) value coeff)).coeff
          ((Finset.univ.filter fun a : α => value a = z).card - 1) = 0 := by
    rw [hzero, map_zero, Polynomial.coeff_zero]
  rw [clearedOccurrences_taylor_coeff_fiber_pred (F := F) value coeff z hfiber] at hcoeff_zero
  have hprod_ne :
      (∏ b ∈ (Finset.univ.filter fun b : α => value b ≠ z), (-z + value b)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro b hb hzero'
    rw [Finset.mem_filter] at hb
    have hsub : value b - z = 0 := by
      simpa [sub_eq_add_neg, add_comm] using hzero'
    exact hb.2 (sub_eq_zero.mp hsub)
  exact (mul_ne_zero hsum hprod_ne) hcoeff_zero

omit [SampleableType F] in
/-- If a value is missing from the table, its `LookupOccur` numerator fiber sum is the negative
lookup multiplicity. -/
theorem lookupOccurNumerator_fiber_sum_of_table_missing
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) {z : F}
    (hmissing : ∀ u : Fin n → Fin 2, z ≠ table u) :
    (∑ a ∈ (Finset.univ.filter fun a : LookupOccur n M =>
        lookupOccurValue table columns a = z), lookupOccurNumerator multiplicity a) =
      - (lookupMultiplicityCount columns z : F) := by
  classical
  rw [Finset.sum_filter]
  let e := LookupOccur.equivSum n M
  calc
    ∑ a : LookupOccur n M,
        (if lookupOccurValue table columns a = z then
          lookupOccurNumerator multiplicity a else 0)
        =
        ∑ x : ((Fin n → Fin 2) ⊕ (Fin M × (Fin n → Fin 2))),
          (if lookupOccurValue table columns (e.symm x) = z then
            lookupOccurNumerator multiplicity (e.symm x) else 0) := by
          exact Fintype.sum_equiv e _ _ (fun x => by simp [e])
    _ =
        (∑ u : Fin n → Fin 2, if table u = z then multiplicity u else 0) +
          ∑ x : Fin M × (Fin n → Fin 2),
            (if columns x.1 x.2 = z then (-1 : F) else 0) := by
          simp [e, LookupOccur.equivSum, lookupOccurValue, lookupOccurNumerator]
    _ =
        ∑ x : Fin M × (Fin n → Fin 2),
          (if columns x.1 x.2 = z then (-1 : F) else 0) := by
          have htable_zero :
              (∑ u : Fin n → Fin 2, if table u = z then multiplicity u else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro u _
            have hne : table u ≠ z := (hmissing u).symm
            simp [hne]
          rw [htable_zero, zero_add]
    _ = - (lookupMultiplicityCount columns z : F) := by
          rw [lookupMultiplicityCount, ← Finset.sum_filter]
          simp [Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq F] [SampleableType F] in
/-- A false LogUp input has a concrete lookup-column value that is absent from the table. -/
theorem exists_missing_column_of_not_inputRelation
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hnotInput : ((stmt, oStmt), ()) ∉ inputRelation F n M) :
    ∃ i : Fin M, ∃ u : Fin n → Fin 2, ∀ v : Fin n → Fin 2,
      MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u ≠
        MvPolynomial.toEvalsZeroOne (oStmt .table).1 v := by
  unfold inputRelation at hnotInput
  simpa [not_forall, not_exists] using hnotInput

omit [Field F] [SampleableType F] in
/-- The multiplicity count of an actually occurring lookup-column value is positive. -/
theorem lookupMultiplicityCount_pos_of_column_value
    (columns : Fin M → (Fin n → Fin 2) → F) (i : Fin M) (u : Fin n → Fin 2) :
    0 < lookupMultiplicityCount columns (columns i u) := by
  rw [lookupMultiplicityCount, Finset.card_pos]
  exact ⟨(i, u), by simp⟩

omit [Field F] [SampleableType F] in
/-- A value absent from the table has table multiplicity zero. -/
theorem tableMultiplicityCount_eq_zero_of_missing
    (table : (Fin n → Fin 2) → F) {a : F} (hmissing : ∀ u, a ≠ table u) :
    tableMultiplicityCount table a = 0 := by
  rw [tableMultiplicityCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _ hu
  exact hmissing u hu.symm

omit [SampleableType F] in
/-- Under the LogUp characteristic bound, a positive lookup multiplicity remains nonzero in `F`. -/
theorem lookupMultiplicityCount_cast_ne_zero_of_pos
    (hcharLarge : M * 2 ^ n < ringChar F)
    (columns : Fin M → (Fin n → Fin 2) → F) {a : F}
    (hpos : 0 < lookupMultiplicityCount columns a) :
    (lookupMultiplicityCount columns a : F) ≠ 0 := by
  have hle : lookupMultiplicityCount columns a ≤ Fintype.card (Fin M × (Fin n → Fin 2)) := by
    rw [lookupMultiplicityCount, ← Finset.card_univ]
    exact Finset.card_filter_le _ _
  have hcard : Fintype.card (Fin M × (Fin n → Fin 2)) = M * 2 ^ n := by
    simp
  have hlt : lookupMultiplicityCount columns a < ringChar F := by
    calc
      lookupMultiplicityCount columns a ≤ Fintype.card (Fin M × (Fin n → Fin 2)) := hle
      _ = M * 2 ^ n := hcard
      _ < ringChar F := hcharLarge
  intro hzero
  have hdvd : ringChar F ∣ lookupMultiplicityCount columns a :=
    (ringChar.spec F (lookupMultiplicityCount columns a)).1 hzero
  exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd

omit [SampleableType F] in
/-- A false input supplies a missing lookup value whose lookup count is positive and nonzero in
the field, while its table count is zero. -/
theorem exists_missing_column_with_nonzero_lookup_count
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hnotInput : ((stmt, oStmt), ()) ∉ inputRelation F n M) :
    ∃ i : Fin M, ∃ u : Fin n → Fin 2,
      (∀ v : Fin n → Fin 2,
        MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u ≠
          MvPolynomial.toEvalsZeroOne (oStmt .table).1 v) ∧
      0 < lookupMultiplicityCount
          (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1)
          (MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u) ∧
      (lookupMultiplicityCount
          (fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1)
          (MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u) : F) ≠ 0 ∧
      tableMultiplicityCount (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
          (MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1 u) = 0 := by
  obtain ⟨i, u, hmissing⟩ :=
    exists_missing_column_of_not_inputRelation (F := F) (n := n) (M := M)
      stmt oStmt hnotInput
  let table := MvPolynomial.toEvalsZeroOne (oStmt .table).1
  let columns : Fin M → (Fin n → Fin 2) → F :=
    fun j => MvPolynomial.toEvalsZeroOne (oStmt (.column j)).1
  let a := columns i u
  have hpos : 0 < lookupMultiplicityCount columns a :=
    lookupMultiplicityCount_pos_of_column_value (F := F) (n := n) (M := M) columns i u
  have hcast : (lookupMultiplicityCount columns a : F) ≠ 0 :=
    lookupMultiplicityCount_cast_ne_zero_of_pos (F := F) (n := n) (M := M)
      stmt.charLarge columns hpos
  have htable :
    tableMultiplicityCount table a = 0 :=
    tableMultiplicityCount_eq_zero_of_missing (F := F) (n := n) table
      (a := a) hmissing
  exact ⟨i, u, hmissing, hpos, hcast, htable⟩

omit [SampleableType F] in
/-- Contrapositive of LogUp's set-inclusion lemma for an arbitrary malicious multiplicity oracle:
if the lookup input is false, the cleared rational identity is not the zero polynomial. -/
theorem clearedLookupIdentity_ne_zero_of_not_input
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : (Fin n → Fin 2) → F)
    (hnotInput : ((stmt, oStmt), ()) ∉ inputRelation F n M) :
    clearedLookupIdentity
        (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
        (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1)
        multiplicity ≠ 0 := by
  classical
  let table := MvPolynomial.toEvalsZeroOne (oStmt .table).1
  let columns : Fin M → (Fin n → Fin 2) → F :=
    fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1
  obtain ⟨i, u, hmissing, hpos, hcast, _htable⟩ :=
    exists_missing_column_with_nonzero_lookup_count (F := F) (n := n) (M := M)
      stmt oStmt hnotInput
  let z := columns i u
  have hfiber : 0 < (Finset.univ.filter fun a : LookupOccur n M =>
      lookupOccurValue table columns a = z).card := by
    rw [Finset.card_pos]
    exact ⟨LookupOccur.column i u, by simp [lookupOccurValue, z, columns]⟩
  have hsum :
      (∑ a ∈ (Finset.univ.filter fun a : LookupOccur n M =>
        lookupOccurValue table columns a = z),
          lookupOccurNumerator multiplicity a) ≠ 0 := by
    have hsum_eq :
        (∑ a ∈ (Finset.univ.filter fun a : LookupOccur n M =>
          lookupOccurValue table columns a = z),
            lookupOccurNumerator multiplicity a) =
          - (lookupMultiplicityCount columns z : F) := by
      refine lookupOccurNumerator_fiber_sum_of_table_missing
        (F := F) (n := n) (M := M) table columns multiplicity ?_
      intro v
      simpa [table, columns, z] using hmissing v
    rw [hsum_eq]
    exact neg_ne_zero.mpr hcast
  change
    clearedOccurrences (F := F)
      (lookupOccurValue table columns)
      (lookupOccurNumerator multiplicity) ≠ 0
  exact clearedOccurrences_ne_zero_of_fiber_sum_ne_zero
    (F := F) (value := lookupOccurValue table columns)
    (coeff := lookupOccurNumerator multiplicity) hfiber hsum

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Degree bound for the cleared lookup identity: every summand omits exactly one denominator
factor from the `(M + 1) * |H|` factors. -/
theorem clearedLookupIdentity_natDegree_le
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) :
    (clearedLookupIdentity table columns multiplicity).natDegree ≤
      (M + 1) * Fintype.card (Fin n → Fin 2) - 1 := by
  classical
  unfold clearedLookupIdentity
  refine (Polynomial.natDegree_sum_le (Finset.univ : Finset (LookupOccur n M))
    (fun a =>
      Polynomial.C (lookupOccurNumerator multiplicity a) *
        ∏ b ∈ Finset.univ.erase a,
          (Polynomial.X + Polynomial.C (lookupOccurValue table columns b)))).trans ?_
  refine Finset.sup_le fun a _ => ?_
  have hprod :
      (∏ b ∈ Finset.univ.erase a,
          (Polynomial.X + Polynomial.C (lookupOccurValue table columns b))).natDegree ≤
        (Finset.univ.erase a).card := by
    refine (Polynomial.natDegree_prod_le (Finset.univ.erase a)
      (fun b => Polynomial.X + Polynomial.C (lookupOccurValue table columns b))).trans ?_
    simp
  calc
    (Polynomial.C (lookupOccurNumerator multiplicity a) *
        ∏ b ∈ Finset.univ.erase a,
          (Polynomial.X + Polynomial.C (lookupOccurValue table columns b))).natDegree
        ≤ (Polynomial.C (lookupOccurNumerator multiplicity a)).natDegree +
            (∏ b ∈ Finset.univ.erase a,
              (Polynomial.X + Polynomial.C (lookupOccurValue table columns b))).natDegree :=
          Polynomial.natDegree_mul_le
    _ ≤ 0 + (Finset.univ.erase a).card :=
          add_le_add (by simp [Polynomial.natDegree_C]) hprod
    _ = (M + 1) * Fintype.card (Fin n → Fin 2) - 1 := by
          rw [zero_add, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
            LookupOccur.card]

omit [SampleableType F] in
/-- Root-count form of the previous two lemmas, restricted to non-pole challenges. -/
theorem clearedLookupIdentity_bad_x_card_le
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (hpoly : clearedLookupIdentity table columns multiplicity ≠ 0) :
    (Finset.univ.filter fun x : F =>
      (∀ u : Fin n → Fin 2, x + table u ≠ 0) ∧
        Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0).card ≤
      (M + 1) * Fintype.card (Fin n → Fin 2) - 1 := by
  classical
  let p := clearedLookupIdentity table columns multiplicity
  have hsubset :
      (Finset.univ.filter fun x : F =>
        (∀ u : Fin n → Fin 2, x + table u ≠ 0) ∧ Polynomial.eval x p = 0).card ≤
        p.roots.toFinset.card := by
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hpoly).mpr hx.2)
  calc
    (Finset.univ.filter fun x : F =>
        (∀ u : Fin n → Fin 2, x + table u ≠ 0) ∧
          Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0).card
        ≤ p.roots.toFinset.card := hsubset
    _ ≤ p.roots.card := Multiset.toFinset_card_le p.roots
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ (M + 1) * Fintype.card (Fin n → Fin 2) - 1 :=
        clearedLookupIdentity_natDegree_le (F := F) (n := n) (M := M)
          table columns multiplicity

omit [SampleableType F] in
/-- The set of denominator-pole challenges for all table and column occurrences has size at most
the number of occurrences. -/
theorem lookupOccur_pole_card_le
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F) :
    (Finset.univ.filter fun x : F =>
      ∃ a : LookupOccur n M, x + lookupOccurValue table columns a = 0).card ≤
      (M + 1) * Fintype.card (Fin n → Fin 2) := by
  classical
  calc
    (Finset.univ.filter fun x : F =>
        ∃ a : LookupOccur n M, x + lookupOccurValue table columns a = 0).card
        ≤ (Finset.univ.image
            (fun a : LookupOccur n M => -lookupOccurValue table columns a)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          obtain ⟨a, ha⟩ := hx
          exact Finset.mem_image.mpr
            ⟨a, Finset.mem_univ a, (eq_neg_of_add_eq_zero_left ha).symm⟩
    _ ≤ Fintype.card (LookupOccur n M) := by
        rw [← Finset.card_univ]
        exact Finset.card_image_le
    _ = (M + 1) * Fintype.card (Fin n → Fin 2) := LookupOccur.card n M

omit [SampleableType F] in
/-- Root-count bound for the cleared lookup identity over all field challenges. -/
theorem clearedLookupIdentity_root_card_le
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (hpoly : clearedLookupIdentity table columns multiplicity ≠ 0) :
    (Finset.univ.filter fun x : F =>
      Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0).card ≤
      (M + 1) * Fintype.card (Fin n → Fin 2) - 1 := by
  classical
  let p := clearedLookupIdentity table columns multiplicity
  have hsubset :
      (Finset.univ.filter fun x : F => Polynomial.eval x p = 0).card ≤
        p.roots.toFinset.card := by
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hpoly).mpr hx)
  calc
    (Finset.univ.filter fun x : F =>
        Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0).card
        ≤ p.roots.toFinset.card := hsubset
    _ ≤ p.roots.card := Multiset.toFinset_card_le p.roots
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ (M + 1) * Fintype.card (Fin n → Fin 2) - 1 :=
        clearedLookupIdentity_natDegree_le (F := F) (n := n) (M := M)
          table columns multiplicity

/-- Uniform `x` bound for the division-safe bad event: either `x` is a denominator pole for some
occurrence, or it is a root of the nonzero cleared lookup identity. -/
theorem clearedLookupIdentity_bad_x_prob_le
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (hpoly : clearedLookupIdentity table columns multiplicity ≠ 0) :
    Pr[fun x : F =>
        (∃ a : LookupOccur n M, x + lookupOccurValue table columns a = 0) ∨
          Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0 | $ᵗ F] ≤
      (((M + 1) * Fintype.card (Fin n → Fin 2) : ℕ) : ENNReal) /
          (Fintype.card F : ENNReal) +
        (((M + 1) * Fintype.card (Fin n → Fin 2) - 1 : ℕ) : ENNReal) /
          (Fintype.card F : ENNReal) := by
  classical
  refine le_trans (probEvent_or_le ($ᵗ F)
    (fun x : F => ∃ a : LookupOccur n M, x + lookupOccurValue table columns a = 0)
    (fun x : F => Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0)) ?_
  rw [probEvent_uniformSample, probEvent_uniformSample]
  exact add_le_add
    (ENNReal.div_le_div_right
      (Nat.cast_le.mpr (lookupOccur_pole_card_le (F := F) (n := n) (M := M) table columns))
      (Fintype.card F : ENNReal))
    (ENNReal.div_le_div_right
      (Nat.cast_le.mpr
        (clearedLookupIdentity_root_card_le (F := F) (n := n) (M := M)
          table columns multiplicity hpoly))
      (Fintype.card F : ENNReal))

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Evaluating the cleared lookup identity away from denominator poles factors as the common
denominator times the original fractional lookup sum. -/
theorem clearedLookupIdentity_eval_eq_prod_mul_fractionalSum
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (x : F)
    (hden :
      ∀ a : LookupOccur n M, x + lookupOccurValue table columns a ≠ 0) :
    Polynomial.eval x (clearedLookupIdentity table columns multiplicity) =
      ((Finset.univ : Finset (LookupOccur n M)).prod
        (fun a => x + lookupOccurValue table columns a)) *
        (Finset.univ : Finset (LookupOccur n M)).sum
          (fun a => lookupOccurNumerator multiplicity a /
            (x + lookupOccurValue table columns a)) := by
  classical
  unfold clearedLookupIdentity
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  calc
    lookupOccurNumerator multiplicity a *
        ∏ b ∈ Finset.univ.erase a, (x + lookupOccurValue table columns b)
        =
      ((x + lookupOccurValue table columns a) *
          ∏ b ∈ Finset.univ.erase a, (x + lookupOccurValue table columns b)) *
        (lookupOccurNumerator multiplicity a /
          (x + lookupOccurValue table columns a)) := by
        field_simp [hden a]
    _ =
      ((Finset.univ : Finset (LookupOccur n M)).prod
          (fun b => x + lookupOccurValue table columns b)) *
        (lookupOccurNumerator multiplicity a /
          (x + lookupOccurValue table columns a)) := by
        rw [Finset.mul_prod_erase (Finset.univ : Finset (LookupOccur n M))
          (fun b => x + lookupOccurValue table columns b) (Finset.mem_univ a)]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Away from denominator poles, a nonzero cleared lookup identity evaluation means the original
fractional lookup sum is nonzero. -/
theorem fractionalSum_ne_zero_of_clearedLookupIdentity_eval_ne_zero
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (x : F)
    (hden :
      ∀ a : LookupOccur n M, x + lookupOccurValue table columns a ≠ 0)
    (heval : Polynomial.eval x (clearedLookupIdentity table columns multiplicity) ≠ 0) :
    (Finset.univ : Finset (LookupOccur n M)).sum
        (fun a => lookupOccurNumerator multiplicity a /
          (x + lookupOccurValue table columns a)) ≠ 0 := by
  intro hsum
  have hfactor :=
    clearedLookupIdentity_eval_eq_prod_mul_fractionalSum
      (F := F) (n := n) (M := M) table columns multiplicity x hden
  rw [hfactor, hsum, mul_zero] at heval
  exact heval rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Conversely to `domainIdentityTerm_eq_zero`, away from the group's denominator poles a zero
domain-identity term forces the helper value to be the fractional partial sum. -/
theorem helper_eq_helperValue_of_domainIdentityTerm_eq_zero
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (k : Fin K) (u : Fin n → Fin 2)
    (hD : domainIdentityTerm groups table columns multiplicity helpers xChallenge k u = 0)
    (hφ : ∀ i ∈ groups k, termPhi table columns xChallenge i u ≠ 0) :
    helpers k u = helperValue groups table columns multiplicity xChallenge k u := by
  classical
  let φ : TermIdx M → F := fun i => termPhi table columns xChallenge i u
  let μ : TermIdx M → F := fun i => termNumerator multiplicity i u
  have hprod_ne : (∏ i ∈ groups k, φ i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact hφ i hi
  unfold domainIdentityTerm at hD
  have hmul :
      helpers k u * (∏ i ∈ groups k, φ i) =
        ∑ i ∈ groups k, μ i * ∏ j ∈ (groups k).erase i, φ j := by
    simpa [φ, μ] using sub_eq_zero.mp hD
  unfold helperValue
  apply mul_right_cancel₀ hprod_ne
  calc
    helpers k u * (∏ i ∈ groups k, φ i)
        = ∑ i ∈ groups k, μ i * ∏ j ∈ (groups k).erase i, φ j := hmul
    _ = (∑ i ∈ groups k, μ i / φ i) * ∏ i ∈ groups k, φ i := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [← Finset.mul_prod_erase (groups k) φ hi]
        field_simp [φ, hφ i hi]
    _ = helperValue groups table columns multiplicity xChallenge k u *
          ∏ i ∈ groups k, φ i := by
        rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Local copy of the protocol-group partition theorem: summing over all concrete helper groups
is the same as summing over all `TermIdx` values. -/
theorem sum_protocolGroups_soundness (params : ProtocolParams M) (g : TermIdx M → F) :
    (∑ k : Fin params.numGroups, ∑ i ∈ params.group k, g i) = ∑ i : TermIdx M, g i := by
  classical
  have hℓ := params.sumSize_pos
  have hidx : ∀ i : TermIdx M, i.val / params.sumSize < params.numGroups := by
    intro i
    have hiM : i.val ≤ M := Nat.lt_succ_iff.mp i.isLt
    have hle : i.val / params.sumSize ≤ M / params.sumSize := Nat.div_le_div_right hiM
    rw [ProtocolParams.numGroups, Nat.add_div_right _ hℓ]
    omega
  rw [← Finset.sum_fiberwise Finset.univ
      (fun i : TermIdx M => (⟨i.val / params.sumSize, hidx i⟩ : Fin params.numGroups)) g]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  ext i
  simp only [ProtocolParams.group, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have ha : k.val ≤ i.val / params.sumSize := (Nat.le_div_iff_mul_le hℓ).mpr h1
    have hb : i.val / params.sumSize < k.val + 1 := (Nat.div_lt_iff_lt_mul hℓ).mpr h2
    omega
  · intro h
    exact ⟨(Nat.le_div_iff_mul_le hℓ).mp (by omega),
      (Nat.div_lt_iff_lt_mul hℓ).mp (by omega)⟩

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Convert a term index and Boolean row into the corresponding denominator occurrence. -/
def termLookupOccur {n M : ℕ} (i : TermIdx M) (u : Fin n → Fin 2) : LookupOccur n M :=
  match termToInput i with
  | .table => .table u
  | .column j => .column j u

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- `TermIdx × H` is the same occurrence set as table rows plus lookup-column rows. -/
def termLookupOccurEquiv (n M : ℕ) :
    (TermIdx M × (Fin n → Fin 2)) ≃ LookupOccur n M where
  toFun p := termLookupOccur p.1 p.2
  invFun
    | .table u => (inputToTerm .table, u)
    | .column j u => (inputToTerm (.column j), u)
  left_inv := by
    rintro ⟨i, u⟩
    unfold termLookupOccur
    cases h : termToInput i with
    | table =>
        have hi : inputToTerm InputIdx.table = i := by
          simpa [h] using (inputToTerm_termToInput i)
        simp [h, hi]
    | column j =>
        have hi : inputToTerm (InputIdx.column j) = i := by
          simpa [h] using (inputToTerm_termToInput i)
        simp [h, hi]
  right_inv := by
    intro a
    cases a with
    | table u =>
        simp [termLookupOccur]
    | column j u =>
        simp [termLookupOccur]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp]
theorem lookupOccurNumerator_termLookupOccur
    (multiplicity : (Fin n → Fin 2) → F) (i : TermIdx M) (u : Fin n → Fin 2) :
    lookupOccurNumerator multiplicity (termLookupOccur i u) =
      termNumerator multiplicity i u := by
  unfold termLookupOccur termNumerator numerator lookupOccurNumerator
  cases termToInput i <;> rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
@[simp]
theorem add_lookupOccurValue_termLookupOccur
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (xChallenge : F) (i : TermIdx M) (u : Fin n → Fin 2) :
    xChallenge + lookupOccurValue table columns (termLookupOccur i u) =
      termPhi table columns xChallenge i u := by
  unfold termLookupOccur termPhi phi lookupOccurValue
  cases termToInput i <;> rfl

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The cleared-identity fractional sum over table/column occurrences is the same as the
row-by-row sum over `TermIdx`. -/
theorem lookupOccur_fractionalSum_eq_sum_termFractions
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (xChallenge : F) :
    (∑ a : LookupOccur n M,
        lookupOccurNumerator multiplicity a / (xChallenge + lookupOccurValue table columns a)) =
      ∑ u : Fin n → Fin 2, ∑ i : TermIdx M,
        termNumerator multiplicity i u / termPhi table columns xChallenge i u := by
  classical
  let e := termLookupOccurEquiv n M
  calc
    (∑ a : LookupOccur n M,
        lookupOccurNumerator multiplicity a / (xChallenge + lookupOccurValue table columns a))
        =
        ∑ p : TermIdx M × (Fin n → Fin 2),
          lookupOccurNumerator multiplicity (e p) /
            (xChallenge + lookupOccurValue table columns (e p)) := by
          exact Fintype.sum_equiv e.symm _ _ (fun a => by simp [e])
    _ =
        ∑ p : TermIdx M × (Fin n → Fin 2),
          termNumerator multiplicity p.1 p.2 / termPhi table columns xChallenge p.1 p.2 := by
          refine Finset.sum_congr rfl ?_
          intro p _
          simp [e, termLookupOccurEquiv]
    _ =
        ∑ i : TermIdx M, ∑ u : Fin n → Fin 2,
          termNumerator multiplicity i u / termPhi table columns xChallenge i u := by
          rw [Fintype.sum_prod_type]
    _ =
        ∑ u : Fin n → Fin 2, ∑ i : TermIdx M,
          termNumerator multiplicity i u / termPhi table columns xChallenge i u := by
          rw [Finset.sum_comm]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- One factor of the Boolean equality polynomial has total degree at most one. -/
theorem singleEqPolynomial_X_totalDegree_le_one (r : F) (i : Fin n) :
    (MvPolynomial.singleEqPolynomial r (MvPolynomial.X i) :
      MvPolynomial (Fin n) F).totalDegree ≤ 1 := by
  rw [MvPolynomial.singleEqPolynomial_nf]
  have hcoeff :
      (MvPolynomial.C (2 : F) * MvPolynomial.C r - 1 :
        MvPolynomial (Fin n) F).totalDegree = 0 := by
    have hconst :
        (MvPolynomial.C (2 : F) * MvPolynomial.C r - 1 :
          MvPolynomial (Fin n) F) =
          MvPolynomial.C (2 * r - 1) := by
      calc
        (MvPolynomial.C (2 : F) * MvPolynomial.C r - 1 :
            MvPolynomial (Fin n) F)
            = MvPolynomial.C (2 * r) - MvPolynomial.C (1 : F) := by simp
        _ = MvPolynomial.C (2 * r - 1) := by
            simp
    calc
      (MvPolynomial.C (2 : F) * MvPolynomial.C r - 1 :
          MvPolynomial (Fin n) F).totalDegree
          = (MvPolynomial.C (2 * r - 1) : MvPolynomial (Fin n) F).totalDegree := by
            exact congrArg MvPolynomial.totalDegree hconst
      _ = 0 := MvPolynomial.totalDegree_C (σ := Fin n) (2 * r - 1)
  have hconst :
      ((1 : MvPolynomial (Fin n) F) - MvPolynomial.C r).totalDegree = 0 := by
    have hconst' :
        ((1 : MvPolynomial (Fin n) F) - MvPolynomial.C r) =
          MvPolynomial.C (1 - r) := by
      simp
    calc
      ((1 : MvPolynomial (Fin n) F) - MvPolynomial.C r).totalDegree
          = (MvPolynomial.C (1 - r) : MvPolynomial (Fin n) F).totalDegree := by
            exact congrArg MvPolynomial.totalDegree hconst'
      _ = 0 := MvPolynomial.totalDegree_C (σ := Fin n) (1 - r)
  calc
    ((MvPolynomial.C (2 : F) * MvPolynomial.C r - 1) * MvPolynomial.X i +
        (1 - MvPolynomial.C r)).totalDegree
        ≤ max (((MvPolynomial.C (2 : F) * MvPolynomial.C r - 1) *
            MvPolynomial.X i).totalDegree)
            ((1 - MvPolynomial.C r : MvPolynomial (Fin n) F).totalDegree) :=
          MvPolynomial.totalDegree_add _ _
    _ ≤ max (0 + 1) 0 := by
          gcongr
          · calc
              (((MvPolynomial.C (2 : F) * MvPolynomial.C r - 1) *
                    MvPolynomial.X i).totalDegree)
                  ≤ (MvPolynomial.C (2 : F) * MvPolynomial.C r - 1).totalDegree +
                      (MvPolynomial.X i : MvPolynomial (Fin n) F).totalDegree :=
                    MvPolynomial.totalDegree_mul _ _
              _ = 0 + 1 := by simp [hcoeff]
          · simp [hconst]
    _ = 1 := by norm_num

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Equality polynomials are multilinear, hence have total degree at most the number of
variables. -/
theorem eqPolynomial_totalDegree_le (r : Fin n → F) :
    (MvPolynomial.eqPolynomial r : MvPolynomial (Fin n) F).totalDegree ≤ n := by
  unfold MvPolynomial.eqPolynomial
  calc
    (∏ i : Fin n, MvPolynomial.singleEqPolynomial (r i) (MvPolynomial.X i)).totalDegree
        ≤ ∑ i : Fin n,
            (MvPolynomial.singleEqPolynomial (r i) (MvPolynomial.X i) :
              MvPolynomial (Fin n) F).totalDegree :=
          MvPolynomial.totalDegree_finsetProd Finset.univ
            (fun i => MvPolynomial.singleEqPolynomial (r i) (MvPolynomial.X i))
    _ ≤ ∑ _i : Fin n, 1 := by
          exact Finset.sum_le_sum fun i _ =>
            singleEqPolynomial_X_totalDegree_le_one (F := F) (n := n) (r i) i
    _ = n := by simp

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Multilinear extensions over the Boolean hypercube have total degree at most `n`. -/
theorem MLE_totalDegree_le (evals : (Fin n → Fin 2) → F) :
    (MvPolynomial.MLE evals : MvPolynomial (Fin n) F).totalDegree ≤ n := by
  unfold MvPolynomial.MLE
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro u _
  calc
    ((MvPolynomial.eqPolynomial (u : Fin n → F) : MvPolynomial (Fin n) F) *
        MvPolynomial.C (evals u)).totalDegree
        ≤ (MvPolynomial.eqPolynomial (u : Fin n → F) : MvPolynomial (Fin n) F).totalDegree +
            (MvPolynomial.C (evals u) : MvPolynomial (Fin n) F).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ n + 0 := by
          gcongr
          · exact eqPolynomial_totalDegree_le (F := F) (n := n) (u : Fin n → F)
          · simp
    _ = n := by simp

/-- Schwartz-Zippel for the verifier's uniform `z : Fin n → F` sampling, phrased in the
`ProbComp` notation used by the protocol proofs. -/
theorem mvPolynomial_uniform_eval_zero_prob_le_div
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) (d : ℕ) (hd : p.totalDegree ≤ d) :
    Pr[fun z : Fin n → F => MvPolynomial.eval z p = 0 | $ᵗ (Fin n → F)] ≤
      (d : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  rw [probEvent_uniformSample]
  have hFpos : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨0⟩
  have hcount :=
    schwartz_zippel_counting (F := F) p hp
      (fun _ : Fin n => (Finset.univ : Finset F)) d (Fintype.card F) hd hFpos
      (fun _ => le_rfl)
  have hpi :
      Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset F)) =
        (Finset.univ : Finset (Fin n → F)) := by
    ext z
    simp
  have hprod :
      (∏ _i : Fin n, (Finset.univ : Finset F).card) =
        Fintype.card (Fin n → F) := by
    simp [Fintype.card_pi]
  have hcount' :
      (Finset.univ.filter fun z : Fin n → F => MvPolynomial.eval z p = 0).card *
          Fintype.card F ≤ d * Fintype.card (Fin n → F) := by
    rw [hpi] at hcount
    simpa [hprod] using hcount
  exact ENNReal.div_le_div_of_mul_le hFpos Fintype.card_pos hcount'

omit [Field F] [DecidableEq F] [SampleableType F] in
/-- Splitting a function table at one coordinate gives that coordinate and all remaining
coordinates. This is the cardinality form used by the batching-root count. -/
theorem finFunction_card_eq_card_mul_rest (K : ℕ) (k₀ : Fin K) :
    Fintype.card (Fin K → F) =
      Fintype.card F * Fintype.card ({k : Fin K // k ≠ k₀} → F) := by
  classical
  let Rest := {k : Fin K // k ≠ k₀} → F
  let split : (Fin K → F) ≃ F × Rest :=
    { toFun := fun lam => (lam k₀, fun k => lam k.1)
      invFun := fun p k => if h : k = k₀ then p.1 else p.2 ⟨k, h⟩
      left_inv := by
        intro lam
        funext k
        by_cases h : k = k₀ <;> simp [h]
      right_inv := by
        intro p
        rcases p with ⟨x, rest⟩
        apply Prod.ext
        · simp
        · funext k
          simp [k.2] }
  calc
    Fintype.card (Fin K → F) = Fintype.card (F × Rest) := Fintype.card_congr split
    _ = Fintype.card F * Fintype.card Rest := Fintype.card_prod F Rest

omit [SampleableType F] in
/-- If one batching coefficient is nonzero, the bad batching scalars are determined by all
coordinates except that coefficient's coordinate. -/
theorem random_linear_batch_bad_card_le_of_coeff_ne_zero (K : ℕ)
    (c₀ : F) (c : Fin K → F) (k₀ : Fin K) (hk₀ : c k₀ ≠ 0) :
    (Finset.univ.filter fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0).card ≤
      Fintype.card ({k : Fin K // k ≠ k₀} → F) := by
  classical
  let bad : Finset (Fin K → F) :=
    Finset.univ.filter fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0
  let Rest := {k : Fin K // k ≠ k₀} → F
  let drop : (Fin K → F) → Rest := fun lam k => lam k.1
  have hdrop_inj : Set.InjOn drop (bad : Set (Fin K → F)) := by
    intro lam hlam mu hmu hdrop
    have hlam_eq : c₀ + ∑ k : Fin K, lam k * c k = 0 := by
      simpa [bad] using (Finset.mem_filter.mp hlam).2
    have hmu_eq : c₀ + ∑ k : Fin K, mu k * c k = 0 := by
      simpa [bad] using (Finset.mem_filter.mp hmu).2
    have hrest : ∀ k : Fin K, k ≠ k₀ → lam k = mu k := by
      intro k hk
      exact congrFun hdrop ⟨k, hk⟩
    have hsum_rest :
        (∑ k ∈ (Finset.univ.erase k₀), lam k * c k) =
          ∑ k ∈ (Finset.univ.erase k₀), mu k * c k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [hrest k (Finset.mem_erase.mp hk).1]
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin K))
        (fun k => lam k * c k) (Finset.mem_univ k₀)] at hlam_eq
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin K))
        (fun k => mu k * c k) (Finset.mem_univ k₀)] at hmu_eq
    have hmu_eq' :
        c₀ + (mu k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k) = 0 := by
      simpa [hsum_rest] using hmu_eq
    have hmain :
        c₀ + (lam k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k) =
          c₀ + (mu k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k) := by
      rw [hlam_eq, hmu_eq']
    have hmul_add :
        lam k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k =
          mu k₀ * c k₀ + ∑ k ∈ (Finset.univ.erase k₀), lam k * c k :=
      add_left_cancel hmain
    have hmul : lam k₀ * c k₀ = mu k₀ * c k₀ := add_right_cancel hmul_add
    funext k
    by_cases hk : k = k₀
    · subst hk
      exact mul_right_cancel₀ hk₀ hmul
    · exact hrest k hk
  calc
    (Finset.univ.filter fun lam : Fin K → F =>
        c₀ + ∑ k : Fin K, lam k * c k = 0).card = bad.card := rfl
    _ ≤ (Finset.univ : Finset Rest).card :=
        Finset.card_le_card_of_injOn drop (fun _ _ => Finset.mem_univ _) hdrop_inj
    _ = Fintype.card Rest := Finset.card_univ

/-- The batched outer sumcheck claim is a random linear combination of the helper-sum claim and
the `K` domain-identity claims, so if one unbatched claim is nonzero the random batching scalar
hits zero with probability at most `1 / |F|`. -/
theorem random_linear_batch_zero_prob_le (K : ℕ)
    (c₀ : F) (c : Fin K → F) (hNonzero : c₀ ≠ 0 ∨ ∃ k, c k ≠ 0) :
    Pr[fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0 | $ᵗ (Fin K → F)] ≤
      ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  by_cases hCoeff : ∃ k, c k ≠ 0
  · obtain ⟨k₀, hk₀⟩ := hCoeff
    rw [probEvent_uniformSample]
    let Rest := {k : Fin K // k ≠ k₀} → F
    have hbad_card :
        (Finset.univ.filter fun lam : Fin K → F =>
          c₀ + ∑ k : Fin K, lam k * c k = 0).card ≤ Fintype.card Rest := by
      simpa [Rest] using
        random_linear_batch_bad_card_le_of_coeff_ne_zero (F := F) K c₀ c k₀ hk₀
    have hcard_domain :
        Fintype.card (Fin K → F) = Fintype.card F * Fintype.card Rest := by
      simpa [Rest] using finFunction_card_eq_card_mul_rest (F := F) K k₀
    have hRest_ne_zero : (Fintype.card Rest : ENNReal) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hRest_ne_top : (Fintype.card Rest : ENNReal) ≠ ⊤ :=
      ENNReal.natCast_ne_top (Fintype.card Rest)
    calc
      ((Finset.univ.filter fun lam : Fin K → F =>
          c₀ + ∑ k : Fin K, lam k * c k = 0).card : ENNReal) /
            Fintype.card (Fin K → F)
          ≤ (Fintype.card Rest : ENNReal) / Fintype.card (Fin K → F) := by
            exact ENNReal.div_le_div_right (Nat.cast_le.mpr hbad_card)
              (Fintype.card (Fin K → F) : ENNReal)
      _ = (Fintype.card Rest : ENNReal) /
            (Fintype.card F * Fintype.card Rest : ℕ) := by
            rw [hcard_domain]
      _ = ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
            rw [Nat.cast_mul]
            simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using
              (ENNReal.mul_div_mul_right (a := (1 : ENNReal))
                (b := (Fintype.card F : ENNReal))
                (c := (Fintype.card Rest : ENNReal)) hRest_ne_zero hRest_ne_top)
  · have hc₀ : c₀ ≠ 0 := by
      rcases hNonzero with hc₀ | hcoeff
      · exact hc₀
      · exact False.elim (hCoeff hcoeff)
    have hzero_coeff : ∀ k : Fin K, c k = 0 := by
      intro k
      by_contra hk
      exact hCoeff ⟨k, hk⟩
    rw [probEvent_uniformSample]
    have hempty :
        (Finset.univ.filter fun lam : Fin K → F =>
          c₀ + ∑ k : Fin K, lam k * c k = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro lam _ hbad
      have hsum_zero : (∑ k : Fin K, lam k * c k) = 0 := by
        simp [hzero_coeff]
      exact hc₀ (by simpa [hsum_zero] using hbad)
    rw [hempty]
    simp

/-! ### The missing `z`-side algebra

The outer sumcheck claim is a random linear batch after the random point `z` has turned each
Boolean-domain identity into evaluation of the identity's multilinear extension. These lemmas make
that decomposition explicit, so the remaining protocol bridge can charge the bad-`x`, bad-`z`, and
bad-`lambda` events separately.
-/

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Scalar product with the equality kernel is evaluation of the multilinear extension. This is
the Boolean-hypercube version of the paper's Lagrange-query to point-query correspondence. -/
theorem sum_eqPolynomial_mul_eq_MLE_eval
    (evals : (Fin n → Fin 2) → F) (z : Fin n → F) :
    (∑ u : Fin n → Fin 2,
        MvPolynomial.eval (u : Fin n → F) (MvPolynomial.eqPolynomial z) * evals u) =
      MvPolynomial.eval z (MvPolynomial.MLE evals) := by
  classical
  unfold MvPolynomial.MLE
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [MvPolynomial.eqPolynomial_symm (x := (u : Fin n → F)) (y := z)]

omit [SampleableType F] in
/-- The multilinear extension of one LogUp domain-identity table. -/
noncomputable def domainIdentityMLE
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (k : Fin K) : MvPolynomial (Fin n) F :=
  MvPolynomial.MLE
    (fun u => domainIdentityTerm groups table columns multiplicity helpers xChallenge k u)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- If a domain-identity MLE is the zero polynomial, then the corresponding row identity is zero
at every Boolean row. -/
theorem domainIdentityTerm_eq_zero_of_domainIdentityMLE_eq_zero
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (k : Fin K)
    (hzero :
      domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
        helpers xChallenge k = 0)
    (u : Fin n → Fin 2) :
    domainIdentityTerm groups table columns multiplicity helpers xChallenge k u = 0 := by
  have hEval := congrArg (fun p : MvPolynomial (Fin n) F =>
    MvPolynomial.eval (u : Fin n → F) p) hzero
  simpa [domainIdentityMLE] using hEval

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- If every domain-identity MLE is the zero polynomial, then the helpers are exactly the
fractional terms, hence their total sum is the cleared-identity fractional sum. -/
theorem helperSum_eq_lookupOccur_fractionalSum_of_domainIdentityMLEs_zero
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (hgroups : ∀ g : TermIdx M → F,
      (∑ k : Fin K, ∑ i ∈ groups k, g i) = ∑ i : TermIdx M, g i)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F)
    (hDzero : ∀ k : Fin K,
      domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
        helpers xChallenge k = 0)
    (hden : ∀ a : LookupOccur n M, xChallenge + lookupOccurValue table columns a ≠ 0) :
    (∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u) =
      ∑ a : LookupOccur n M,
        lookupOccurNumerator multiplicity a / (xChallenge + lookupOccurValue table columns a) := by
  classical
  calc
    (∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u)
        =
        ∑ u : Fin n → Fin 2, ∑ k : Fin K,
          helperValue groups table columns multiplicity xChallenge k u := by
          refine Finset.sum_congr rfl ?_
          intro u _
          refine Finset.sum_congr rfl ?_
          intro k _
          exact helper_eq_helperValue_of_domainIdentityTerm_eq_zero
            (F := F) (n := n) (M := M) groups table columns multiplicity helpers
            xChallenge k u
            (domainIdentityTerm_eq_zero_of_domainIdentityMLE_eq_zero
              (F := F) (n := n) (M := M) groups table columns multiplicity helpers
              xChallenge k (hDzero k) u)
            (fun i hi => by
              have h := hden (termLookupOccur i u)
              simpa using h)
    _ =
        ∑ u : Fin n → Fin 2, ∑ k : Fin K, ∑ i ∈ groups k,
          termNumerator multiplicity i u / termPhi table columns xChallenge i u := by
          simp [helperValue]
    _ =
        ∑ u : Fin n → Fin 2, ∑ i : TermIdx M,
          termNumerator multiplicity i u / termPhi table columns xChallenge i u := by
          refine Finset.sum_congr rfl ?_
          intro u _
          exact hgroups
            (fun i => termNumerator multiplicity i u / termPhi table columns xChallenge i u)
    _ =
        ∑ a : LookupOccur n M,
          lookupOccurNumerator multiplicity a /
            (xChallenge + lookupOccurValue table columns a) := by
          exact (lookupOccur_fractionalSum_eq_sum_termFractions
            (F := F) (n := n) (M := M) table columns multiplicity xChallenge).symm

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- If the helper zero-sum vanishes but the global fractional LogUp sum is nonzero, then at least
one domain-identity MLE is a nonzero polynomial. -/
theorem exists_nonzero_domainIdentityMLE_of_helperSum_zero_of_fractionalSum_ne_zero
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (hgroups : ∀ g : TermIdx M → F,
      (∑ k : Fin K, ∑ i ∈ groups k, g i) = ∑ i : TermIdx M, g i)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F)
    (hden : ∀ a : LookupOccur n M, xChallenge + lookupOccurValue table columns a ≠ 0)
    (hhelper :
      (∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u) = 0)
    (hfractional :
      (∑ a : LookupOccur n M,
        lookupOccurNumerator multiplicity a / (xChallenge + lookupOccurValue table columns a))
          ≠ 0) :
    ∃ k : Fin K,
      domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
        helpers xChallenge k ≠ 0 := by
  classical
  by_contra hnone
  have hDzero : ∀ k : Fin K,
      domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
        helpers xChallenge k = 0 := by
    intro k
    by_contra hk
    exact hnone ⟨k, hk⟩
  have hsum := helperSum_eq_lookupOccur_fractionalSum_of_domainIdentityMLEs_zero
    (F := F) (n := n) (M := M) groups hgroups table columns multiplicity helpers
    xChallenge hDzero hden
  exact hfractional (by simpa [hhelper] using hsum.symm)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- The scalar product used by the outer claim for one domain identity is the corresponding MLE
evaluated at the sampled point `z`. -/
theorem domainIdentityKernelClaim_eq_eval_domainIdentityMLE
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (zChallenge : Fin n → F) (k : Fin K) :
    (∑ u : Fin n → Fin 2,
        MvPolynomial.eval (u : Fin n → F) (MvPolynomial.eqPolynomial zChallenge) *
          domainIdentityTerm groups table columns multiplicity helpers xChallenge k u) =
      MvPolynomial.eval zChallenge
        (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
          helpers xChallenge k) := by
  exact sum_eqPolynomial_mul_eq_MLE_eval (F := F) (n := n)
    (fun u => domainIdentityTerm groups table columns multiplicity helpers xChallenge k u)
    zChallenge

/-- A nonzero domain-identity MLE vanishes at a uniformly sampled `z` with the standard
Schwartz-Zippel multilinear bound `n / |F|`. -/
theorem domainIdentityMLE_eval_zero_prob_le
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (k : Fin K)
    (hpoly :
      domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
        helpers xChallenge k ≠ 0) :
    Pr[fun z : Fin n → F =>
        MvPolynomial.eval z
          (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
            helpers xChallenge k) = 0 | $ᵗ (Fin n → F)] ≤
      (n : ENNReal) / (Fintype.card F : ENNReal) := by
  exact mvPolynomial_uniform_eval_zero_prob_le_div (F := F) (n := n)
    (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity helpers
      xChallenge k) hpoly n
    (by
      unfold domainIdentityMLE
      exact MLE_totalDegree_le (F := F) (n := n)
        (fun u => domainIdentityTerm groups table columns multiplicity helpers xChallenge k u))

/-- Union bound over the `K` domain-identity MLEs: the chance that any nonzero one vanishes at
the sampled `z` is at most `K * n / |F|`. -/
theorem domainIdentityMLE_exists_bad_z_prob_le
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) :
    Pr[fun z : Fin n → F =>
        ∃ k : Fin K,
          domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
              helpers xChallenge k ≠ 0 ∧
            MvPolynomial.eval z
              (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
                helpers xChallenge k) = 0 | $ᵗ (Fin n → F)] ≤
      (K : ENNReal) * ((n : ENNReal) / (Fintype.card F : ENNReal)) := by
  classical
  let P : Fin K → MvPolynomial (Fin n) F :=
    fun k => domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
      helpers xChallenge k
  calc
    Pr[fun z : Fin n → F => ∃ k : Fin K, P k ≠ 0 ∧ MvPolynomial.eval z (P k) = 0 |
        $ᵗ (Fin n → F)]
        ≤
        ∑ k : Fin K,
          Pr[fun z : Fin n → F => P k ≠ 0 ∧ MvPolynomial.eval z (P k) = 0 |
            $ᵗ (Fin n → F)] := by
          simpa [P] using
            (probEvent_exists_finset_le_sum
              (m := ProbComp) (s := (Finset.univ : Finset (Fin K))) ($ᵗ (Fin n → F))
              (fun k z => P k ≠ 0 ∧ MvPolynomial.eval z (P k) = 0))
    _ ≤
        ∑ _k : Fin K, (n : ENNReal) / (Fintype.card F : ENNReal) := by
          refine Finset.sum_le_sum ?_
          intro k _
          by_cases hpoly : P k = 0
          · have hfalse :
                (fun z : Fin n → F => P k ≠ 0 ∧ MvPolynomial.eval z (P k) = 0) =
                  fun _ => False := by
              funext z
              apply propext
              constructor
              · intro hz
                exact False.elim (hz.1 hpoly)
              · intro h
                exact False.elim h
            rw [hfalse]
            simp
          · refine le_trans (probEvent_mono'' ?_)
              (domainIdentityMLE_eval_zero_prob_le (F := F) (n := n) (M := M)
                groups table columns multiplicity helpers xChallenge k hpoly)
            intro z hz
            exact hz.2
    _ = (K : ENNReal) * ((n : ENNReal) / (Fintype.card F : ENNReal)) := by
        simp [Finset.card_univ, nsmul_eq_mul]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- If the cleared lookup identity is nonzero at `x` and `z` does not hide any nonzero domain
identity, then the linear batching equation has a nonzero constant term or a nonzero coefficient. -/
theorem outer_batch_coefficients_nontrivial_of_good_xz
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (hgroups : ∀ g : TermIdx M → F,
      (∑ k : Fin K, ∑ i ∈ groups k, g i) = ∑ i : TermIdx M, g i)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (zChallenge : Fin n → F)
    (hden : ∀ a : LookupOccur n M, xChallenge + lookupOccurValue table columns a ≠ 0)
    (heval : Polynomial.eval xChallenge
      (clearedLookupIdentity table columns multiplicity) ≠ 0)
    (hzGood : ∀ k : Fin K,
      domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
          helpers xChallenge k ≠ 0 →
        MvPolynomial.eval zChallenge
          (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
            helpers xChallenge k) ≠ 0) :
    (∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u) ≠ 0 ∨
      ∃ k : Fin K,
        MvPolynomial.eval zChallenge
          (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
            helpers xChallenge k) ≠ 0 := by
  classical
  letI : DecidableEq F := Classical.decEq F
  let c0 : F := ∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u
  by_cases hhelper : c0 = 0
  · right
    have hhelper' :
        (∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u) = 0 := by
      simpa [c0] using hhelper
    have hfractional :=
      fractionalSum_ne_zero_of_clearedLookupIdentity_eval_ne_zero
        (F := F) (n := n) (M := M) table columns multiplicity xChallenge hden heval
    obtain ⟨k, hk⟩ :=
      exists_nonzero_domainIdentityMLE_of_helperSum_zero_of_fractionalSum_ne_zero
        (F := F) (n := n) (M := M) groups hgroups table columns multiplicity helpers
        xChallenge hden hhelper' hfractional
    exact ⟨k, hzGood k hk⟩
  · exact Or.inl (by
      intro hsum
      exact hhelper (by simpa [c0] using hsum))

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Deterministic core of outer soundness. If `x` makes the cleared lookup identity nonzero,
`z` does not hide any nonzero domain-identity MLE, and `lambda` avoids the resulting nontrivial
linear equation, then the expanded outer sumcheck claim is nonzero. -/
theorem outer_linear_claim_ne_zero_of_good_challenges
    {K : ℕ} (groups : Fin K → Finset (TermIdx M))
    (hgroups : ∀ g : TermIdx M → F,
      (∑ k : Fin K, ∑ i ∈ groups k, g i) = ∑ i : TermIdx M, g i)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (zChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (hden : ∀ a : LookupOccur n M, xChallenge + lookupOccurValue table columns a ≠ 0)
    (heval : Polynomial.eval xChallenge
      (clearedLookupIdentity table columns multiplicity) ≠ 0)
    (hzGood : ∀ k : Fin K,
      domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
          helpers xChallenge k ≠ 0 →
        MvPolynomial.eval zChallenge
          (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
            helpers xChallenge k) ≠ 0)
    (hBatchGood :
      ((∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u) ≠ 0 ∨
          ∃ k : Fin K,
            MvPolynomial.eval zChallenge
              (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns
                multiplicity helpers xChallenge k) ≠ 0) →
        (∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u) +
            ∑ k : Fin K,
              batchingScalars k *
                MvPolynomial.eval zChallenge
                  (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns
                    multiplicity helpers xChallenge k) ≠ 0) :
    (∑ u : Fin n → Fin 2, ∑ k : Fin K, helpers k u) +
        ∑ k : Fin K,
          batchingScalars k *
            MvPolynomial.eval zChallenge
              (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
                helpers xChallenge k) ≠ 0 := by
  classical
  letI : DecidableEq F := Classical.decEq F
  exact hBatchGood
    (outer_batch_coefficients_nontrivial_of_good_xz
      (F := F) (n := n) (M := M) groups hgroups table columns multiplicity helpers
      xChallenge zChallenge hden heval hzGood)

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Expanding the outer sumcheck claim: after `x` and `z` are fixed it is a linear polynomial in
the batching scalars. The constant term is the helper zero-sum claim, and the coefficients are the
`z`-evaluated domain-identity MLEs. -/
theorem logupOuterSumcheckClaim_eq_linear_batch
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    logupOuterSumcheckClaim F n M params stmt oStmt =
      (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups,
        MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1 u) +
        ∑ k : Fin params.numGroups,
          stmt.batchingScalars k *
            MvPolynomial.eval stmt.zChallenge
              (domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
                (MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1)
                (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1)
                (MvPolynomial.toEvalsZeroOne (oStmt .multiplicity).1)
                (fun k => MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1)
                stmt.xChallenge k) := by
  classical
  unfold logupOuterSumcheckClaim
  simp_rw [logupQPolynomial_eval_hypercube]
  unfold qOnHypercube
  let table : (Fin n → Fin 2) → F :=
    MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1
  let columns : Fin M → (Fin n → Fin 2) → F :=
    fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1
  let multiplicity : (Fin n → Fin 2) → F :=
    MvPolynomial.toEvalsZeroOne (oStmt .multiplicity).1
  let helpers : Fin params.numGroups → (Fin n → Fin 2) → F :=
    fun k => MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1
  let L : (Fin n → Fin 2) → F :=
    fun u => MvPolynomial.eval (u : Fin n → F) (MvPolynomial.eqPolynomial stmt.zChallenge)
  let D : Fin params.numGroups → (Fin n → Fin 2) → F :=
    fun k u => domainIdentityTerm params.group table columns multiplicity helpers
      stmt.xChallenge k u
  change
    (∑ u : Fin n → Fin 2,
        ∑ k : Fin params.numGroups,
          (helpers k u + L u * stmt.batchingScalars k * D k u)) =
      (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups, helpers k u) +
        ∑ k : Fin params.numGroups,
          stmt.batchingScalars k *
            MvPolynomial.eval stmt.zChallenge
              (domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
                table columns multiplicity helpers stmt.xChallenge k)
  calc
    (∑ u : Fin n → Fin 2,
        ∑ k : Fin params.numGroups,
          (helpers k u + L u * stmt.batchingScalars k * D k u))
        =
      ∑ u : Fin n → Fin 2,
        ((∑ k : Fin params.numGroups,
          helpers k u) +
          ∑ k : Fin params.numGroups,
            L u * stmt.batchingScalars k * D k u) := by
        refine Finset.sum_congr rfl ?_
        intro u _
        rw [← Finset.sum_add_distrib]
    _ =
      (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups,
        helpers k u) +
        ∑ u : Fin n → Fin 2,
          ∑ k : Fin params.numGroups,
            L u * stmt.batchingScalars k * D k u := by
        rw [Finset.sum_add_distrib]
    _ =
      (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups,
        helpers k u) +
        ∑ k : Fin params.numGroups,
          stmt.batchingScalars k *
            (∑ u : Fin n → Fin 2,
              L u * D k u) := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        calc
          (∑ x : Fin n → Fin 2, L x * stmt.batchingScalars k * D k x)
              = ∑ x : Fin n → Fin 2, stmt.batchingScalars k * (L x * D k x) := by
                refine Finset.sum_congr rfl ?_
                intro u _
                ring
          _ = stmt.batchingScalars k * ∑ u : Fin n → Fin 2, L u * D k u := by
                rw [Finset.mul_sum]
    _ =
      (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups,
        helpers k u) +
        ∑ k : Fin params.numGroups,
          stmt.batchingScalars k *
            MvPolynomial.eval stmt.zChallenge
              (domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
                table columns multiplicity helpers stmt.xChallenge k) := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [domainIdentityKernelClaim_eq_eval_domainIdentityMLE]

omit [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Protocol-shaped deterministic core: a concrete outer transcript cannot satisfy the mid
relation when the three challenge checks are all good. -/
theorem logupOuterSumcheckClaim_ne_zero_of_good_challenges
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (hden :
      ∀ a : LookupOccur n M,
        stmt.xChallenge +
            lookupOccurValue
              (MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1)
              (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1) a ≠ 0)
    (heval :
      Polynomial.eval stmt.xChallenge
        (clearedLookupIdentity
          (MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1)
          (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1)
          (MvPolynomial.toEvalsZeroOne (oStmt .multiplicity).1)) ≠ 0)
    (hzGood :
      ∀ k : Fin params.numGroups,
        domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
            (MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1)
            (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1)
            (MvPolynomial.toEvalsZeroOne (oStmt .multiplicity).1)
            (fun k => MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1)
            stmt.xChallenge k ≠ 0 →
          MvPolynomial.eval stmt.zChallenge
            (domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
              (MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1)
              (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1)
              (MvPolynomial.toEvalsZeroOne (oStmt .multiplicity).1)
              (fun k => MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1)
              stmt.xChallenge k) ≠ 0)
    (hBatchGood :
      ((∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups,
            MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1 u) ≠ 0 ∨
          ∃ k : Fin params.numGroups,
            MvPolynomial.eval stmt.zChallenge
              (domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
                (MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1)
                (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1)
                (MvPolynomial.toEvalsZeroOne (oStmt .multiplicity).1)
                (fun k => MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1)
                stmt.xChallenge k) ≠ 0) →
        (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups,
            MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1 u) +
          ∑ k : Fin params.numGroups,
            stmt.batchingScalars k *
              MvPolynomial.eval stmt.zChallenge
                (domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
                  (MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1)
                  (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1)
                  (MvPolynomial.toEvalsZeroOne (oStmt .multiplicity).1)
                  (fun k => MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1)
                  stmt.xChallenge k) ≠ 0) :
    logupOuterSumcheckClaim F n M params stmt oStmt ≠ 0 := by
  classical
  let table : (Fin n → Fin 2) → F :=
    MvPolynomial.toEvalsZeroOne (oStmt (.input .table)).1
  let columns : Fin M → (Fin n → Fin 2) → F :=
    fun i => MvPolynomial.toEvalsZeroOne (oStmt (.input (.column i))).1
  let multiplicity : (Fin n → Fin 2) → F :=
    MvPolynomial.toEvalsZeroOne (oStmt .multiplicity).1
  let helpers : Fin params.numGroups → (Fin n → Fin 2) → F :=
    fun k => MvPolynomial.toEvalsZeroOne (oStmt .helpers k).1
  letI : DecidableEq F := Classical.decEq F
  have hlinear :=
    outer_linear_claim_ne_zero_of_good_challenges
      (F := F) (n := n) (M := M) (K := params.numGroups) (params.group)
      (sum_protocolGroups_soundness (F := F) (M := M) params) table columns multiplicity helpers
      stmt.xChallenge stmt.zChallenge stmt.batchingScalars
      (by simpa [table, columns] using hden)
      (by simpa [table, columns, multiplicity] using heval)
      (by simpa [table, columns, multiplicity, helpers] using hzGood)
      (by simpa [table, columns, multiplicity, helpers] using hBatchGood)
  rw [logupOuterSumcheckClaim_eq_linear_batch]
  simpa [table, columns, multiplicity, helpers] using hlinear

omit σ init impl [DecidableEq F] [SampleableType F] in
/-- Simulating the scan-free outer verifier leaves only the public challenge data packaged as the
outer statement. -/
theorem outerVerify_simulateQ_eq_soundness (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (messages : ∀ i, (outerPSpec F n params).Message i)
    (challenges : ∀ i, (outerPSpec F n params).Challenge i) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)
        ((outerVerifier oSpec F n M params).verify stmt challenges)
      = (do
          let x : F := challenges (outerChallengeXIdx F n M params)
          let batch : BatchingChallenge F n params.numGroups :=
            challenges (outerChallengeBatchIdx F n M params)
          pure { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }
        : OptionT (OracleComp oSpec) (StmtAfterOuter F n M params)) := by
  simp [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx]
  rfl

omit oSpec F n M params σ init impl [Field F] [Fintype F] [DecidableEq F] [SampleableType F] in
/-- Four-round unfolding of `Fin.induction`, used when expanding the outer protocol run. -/
private theorem Fin.induction_four_soundness {motive : Fin 5 → Sort*} {zero : motive 0}
    {succ : ∀ i : Fin 4, motive i.castSucc → motive i.succ} :
    Fin.induction (motive := motive) zero succ (Fin.last 4)
      = succ 3 (succ 2 (succ 1 (succ 0 zero))) := rfl

private def outerBadX
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (x : F) : Prop :=
  (∃ a : LookupOccur n M, x + lookupOccurValue table columns a = 0) ∨
    Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0

private noncomputable def outerBadZ
    (groups : Fin params.numGroups → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin params.numGroups → (Fin n → Fin 2) → F)
    (x : F) (z : Fin n → F) : Prop :=
  ∃ k : Fin params.numGroups,
    domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity helpers x k ≠ 0 ∧
      MvPolynomial.eval z
        (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns multiplicity
          helpers x k) = 0

private noncomputable def outerBadBatch
    (groups : Fin params.numGroups → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin params.numGroups → (Fin n → Fin 2) → F)
    (x : F) (z : Fin n → F) (lam : Fin params.numGroups → F) : Prop :=
  (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups, helpers k u) +
      ∑ k : Fin params.numGroups,
        lam k *
          MvPolynomial.eval z
            (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns
              multiplicity helpers x k) =
    0

private theorem outerBadBatch_prob_le
    (hBatch :
      ∀ (K : ℕ) (c₀ : F) (c : Fin K → F),
        c₀ ≠ 0 ∨ (∃ k, c k ≠ 0) →
          Pr[fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0 |
              $ᵗ (Fin K → F)] ≤
            ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal))
    (groups : Fin params.numGroups → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin params.numGroups → (Fin n → Fin 2) → F)
    (x : F) (z : Fin n → F)
    (hNontriv :
      (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups, helpers k u) ≠ 0 ∨
        ∃ k : Fin params.numGroups,
          MvPolynomial.eval z
            (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns
              multiplicity helpers x k) ≠ 0) :
    Pr[fun lam : Fin params.numGroups → F =>
        outerBadBatch (F := F) (n := n) (M := M) (params := params)
          groups table columns multiplicity helpers x z lam | $ᵗ (Fin params.numGroups → F)] ≤
      ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  simpa [outerBadBatch] using
    hBatch params.numGroups
      (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups, helpers k u)
      (fun k : Fin params.numGroups =>
        MvPolynomial.eval z
          (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns
            multiplicity helpers x k))
      hNontriv

private theorem outerBadBatch_given_good_z_prob_le [Inhabited F]
    (hBatch :
      ∀ (K : ℕ) (c₀ : F) (c : Fin K → F),
        c₀ ≠ 0 ∨ (∃ k, c k ≠ 0) →
          Pr[fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0 |
              $ᵗ (Fin K → F)] ≤
            ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal))
    (groups : Fin params.numGroups → Finset (TermIdx M))
    (hgroups : ∀ g : TermIdx M → F,
      (∑ k : Fin params.numGroups, ∑ i ∈ groups k, g i) = ∑ i : TermIdx M, g i)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin params.numGroups → (Fin n → Fin 2) → F)
    (x : F)
    (hden : ∀ a : LookupOccur n M, x + lookupOccurValue table columns a ≠ 0)
    (heval : Polynomial.eval x (clearedLookupIdentity table columns multiplicity) ≠ 0) :
    Pr[fun batch : BatchingChallenge F n params.numGroups =>
        ¬ outerBadZ (F := F) (n := n) (M := M) (params := params)
            groups table columns multiplicity helpers x batch.1 ∧
          outerBadBatch (F := F) (n := n) (M := M) (params := params)
            groups table columns multiplicity helpers x batch.1 batch.2 |
        $ᵗ (BatchingChallenge F n params.numGroups)] ≤
      ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  change
    Pr[fun batch : (Fin n → F) × (Fin params.numGroups → F) =>
        ¬ outerBadZ (F := F) (n := n) (M := M) (params := params)
            groups table columns multiplicity helpers x batch.1 ∧
          outerBadBatch (F := F) (n := n) (M := M) (params := params)
            groups table columns multiplicity helpers x batch.1 batch.2 |
        (Prod.mk <$> ($ᵗ (Fin n → F)) <*> ($ᵗ (Fin params.numGroups → F)))] ≤
      ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal)
  rw [show (Prod.mk <$> ($ᵗ (Fin n → F)) <*> ($ᵗ (Fin params.numGroups → F))) =
      (do
        let z ← $ᵗ (Fin n → F)
        let lam ← $ᵗ (Fin params.numGroups → F)
        pure (z, lam)) by
        simp [seq_eq_bind_map]]
  refine probEvent_bind_le_of_forall_le ?_
  intro z _hz
  by_cases hzBad :
      outerBadZ (F := F) (n := n) (M := M) (params := params)
        groups table columns multiplicity helpers x z
  · have hfalse :
        (fun batch : (Fin n → F) × (Fin params.numGroups → F) =>
            ¬ outerBadZ (F := F) (n := n) (M := M) (params := params)
                groups table columns multiplicity helpers x batch.1 ∧
              outerBadBatch (F := F) (n := n) (M := M) (params := params)
                groups table columns multiplicity helpers x batch.1 batch.2) ∘
            (fun lam : Fin params.numGroups → F => (z, lam)) =
          fun _ => False := by
        funext lam
        simp [hzBad]
    rw [show (do
          let lam ← $ᵗ (Fin params.numGroups → F)
          pure (z, lam)) =
        (($ᵗ (Fin params.numGroups → F)) >>=
          (pure ∘ fun lam : Fin params.numGroups → F => (z, lam))) by rfl]
    rw [probEvent_bind_pure_comp]
    rw [hfalse]
    simp
  · have hzGood :
        ∀ k : Fin params.numGroups,
          domainIdentityMLE (F := F) (n := n) (M := M) groups table columns
              multiplicity helpers x k ≠ 0 →
            MvPolynomial.eval z
              (domainIdentityMLE (F := F) (n := n) (M := M) groups table columns
                multiplicity helpers x k) ≠ 0 := by
      intro k hk hzero
      exact hzBad ⟨k, hk, hzero⟩
    have hNontriv :=
      outer_batch_coefficients_nontrivial_of_good_xz
        (F := F) (n := n) (M := M) (K := params.numGroups)
        groups hgroups
        table columns multiplicity helpers x z hden heval hzGood
    have hLam :=
      outerBadBatch_prob_le (F := F) (n := n) (M := M) (params := params)
        hBatch groups table columns multiplicity helpers x z hNontriv
    rw [show (do
          let lam ← $ᵗ (Fin params.numGroups → F)
          pure (z, lam)) =
        (($ᵗ (Fin params.numGroups → F)) >>=
          (pure ∘ fun lam : Fin params.numGroups → F => (z, lam))) by rfl]
    rw [probEvent_bind_pure_comp]
    simpa [Function.comp_def, hzBad] using hLam

private theorem outerBatchChallenge_bad_prob_le [Inhabited F]
    (hBatch :
      ∀ (K : ℕ) (c₀ : F) (c : Fin K → F),
        c₀ ≠ 0 ∨ (∃ k, c k ≠ 0) →
          Pr[fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0 |
              $ᵗ (Fin K → F)] ≤
            ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal))
    (groups : Fin params.numGroups → Finset (TermIdx M))
    (hgroups : ∀ g : TermIdx M → F,
      (∑ k : Fin params.numGroups, ∑ i ∈ groups k, g i) = ∑ i : TermIdx M, g i)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin params.numGroups → (Fin n → Fin 2) → F)
    (x : F)
    (hden : ∀ a : LookupOccur n M, x + lookupOccurValue table columns a ≠ 0)
    (heval : Polynomial.eval x (clearedLookupIdentity table columns multiplicity) ≠ 0) :
    Pr[fun batch : BatchingChallenge F n params.numGroups =>
        outerBadZ (F := F) (n := n) (M := M) (params := params)
            groups table columns multiplicity helpers x batch.1 ∨
          outerBadBatch (F := F) (n := n) (M := M) (params := params)
            groups table columns multiplicity helpers x batch.1 batch.2 |
        $ᵗ (BatchingChallenge F n params.numGroups)] ≤
      ((params.numGroups : ENNReal) * ((n : ENNReal) / (Fintype.card F : ENNReal))) +
        ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  let badZ : (Fin n → F) → Prop :=
    outerBadZ (F := F) (n := n) (M := M) (params := params)
      groups table columns multiplicity helpers x
  let badBatch : (Fin n → F) → (Fin params.numGroups → F) → Prop :=
    outerBadBatch (F := F) (n := n) (M := M) (params := params)
      groups table columns multiplicity helpers x
  have hZMarginal :
      Pr[fun batch : BatchingChallenge F n params.numGroups => badZ batch.1 |
          $ᵗ (BatchingChallenge F n params.numGroups)] =
        Pr[badZ | $ᵗ (Fin n → F)] := by
    rw [show (fun batch : BatchingChallenge F n params.numGroups => badZ batch.1) =
        badZ ∘ Prod.fst by rfl]
    rw [← probEvent_map]
    rw [probEvent_def, probEvent_def]
    exact congrArg
      (fun d : SPMF (Fin n → F) =>
        d.run.toOuterMeasure (some '' {x | badZ x}))
      (evalDist_map_fst_uniformSample_prod
        (α := Fin n → F) (β := Fin params.numGroups → F))
  have hZ :
      Pr[fun batch : BatchingChallenge F n params.numGroups => badZ batch.1 |
          $ᵗ (BatchingChallenge F n params.numGroups)] ≤
        (params.numGroups : ENNReal) * ((n : ENNReal) / (Fintype.card F : ENNReal)) := by
    rw [hZMarginal]
    simpa [badZ, outerBadZ] using
      domainIdentityMLE_exists_bad_z_prob_le
        (F := F) (n := n) (M := M) (K := params.numGroups)
        groups table columns multiplicity helpers x
  have hLam :
      Pr[fun batch : BatchingChallenge F n params.numGroups =>
          ¬ badZ batch.1 ∧ badBatch batch.1 batch.2 |
          $ᵗ (BatchingChallenge F n params.numGroups)] ≤
        ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
    simpa [badZ, badBatch] using
      outerBadBatch_given_good_z_prob_le
        (F := F) (n := n) (M := M) (params := params)
        hBatch groups hgroups table columns multiplicity helpers x hden heval
  calc
    Pr[fun batch : BatchingChallenge F n params.numGroups =>
        badZ batch.1 ∨ badBatch batch.1 batch.2 |
        $ᵗ (BatchingChallenge F n params.numGroups)]
        ≤
        Pr[fun batch : BatchingChallenge F n params.numGroups =>
            badZ batch.1 ∨ (¬ badZ batch.1 ∧ badBatch batch.1 batch.2) |
            $ᵗ (BatchingChallenge F n params.numGroups)] := by
          refine probEvent_mono'' ?_
          intro batch h
          by_cases hz : badZ batch.1
          · exact Or.inl hz
          · exact Or.inr ⟨hz, h.resolve_left hz⟩
    _ ≤
        Pr[fun batch : BatchingChallenge F n params.numGroups => badZ batch.1 |
            $ᵗ (BatchingChallenge F n params.numGroups)] +
          Pr[fun batch : BatchingChallenge F n params.numGroups =>
            ¬ badZ batch.1 ∧ badBatch batch.1 batch.2 |
            $ᵗ (BatchingChallenge F n params.numGroups)] := by
          exact probEvent_or_le _ _ _
    _ ≤
        (params.numGroups : ENNReal) * ((n : ENNReal) / (Fintype.card F : ENNReal)) +
          ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal) := by
          exact add_le_add hZ hLam

private def outerTranscriptMultiplicity
    (tr : (outerPSpec F n params).Transcript (1 : Fin 5)) : MultiplicityMessage F n :=
  tr ⟨0, by decide⟩

private def outerTranscriptMultiplicityAt2
    (tr : (outerPSpec F n params).Transcript (2 : Fin 5)) : MultiplicityMessage F n :=
  tr ⟨0, by decide⟩

private def outerTranscriptXAt2
    (tr : (outerPSpec F n params).Transcript (2 : Fin 5)) : F :=
  tr ⟨1, by decide⟩

private def outerTranscriptMultiplicityAt3
    (tr : (outerPSpec F n params).Transcript (3 : Fin 5)) : MultiplicityMessage F n :=
  tr ⟨0, by decide⟩

private def outerTranscriptXAt3
    (tr : (outerPSpec F n params).Transcript (3 : Fin 5)) : F :=
  tr ⟨1, by decide⟩

private def outerTranscriptHelpersAt3
    (tr : (outerPSpec F n params).Transcript (3 : Fin 5)) :
    HelperMessages F n params.numGroups :=
  tr ⟨2, by decide⟩

private def outerTranscriptMultiplicityFull
    (tr : (outerPSpec F n params).FullTranscript) : MultiplicityMessage F n :=
  tr ⟨0, by decide⟩

private def outerTranscriptXFull
    (tr : (outerPSpec F n params).FullTranscript) : F :=
  tr ⟨1, by decide⟩

private def outerTranscriptHelpersFull
    (tr : (outerPSpec F n params).FullTranscript) : HelperMessages F n params.numGroups :=
  tr ⟨2, by decide⟩

private def outerTranscriptBatchFull
    (tr : (outerPSpec F n params).FullTranscript) : BatchingChallenge F n params.numGroups :=
  tr ⟨3, by decide⟩

private noncomputable def outerSoundnessState
    (stmtPair : StmtIn F n M × (∀ i, OStmtIn F n M i)) :
    (m : Fin 5) → (outerPSpec F n params).Transcript m → Prop
  | ⟨0, _⟩, _ => stmtPair ∈ (inputRelation F n M).language
  | ⟨1, _⟩, _ => stmtPair ∈ (inputRelation F n M).language
  | ⟨2, _⟩, tr =>
      stmtPair ∈ (inputRelation F n M).language ∨
        outerBadX (F := F) (n := n) (M := M)
          (MvPolynomial.toEvalsZeroOne (stmtPair.2 .table).1)
          (fun i => MvPolynomial.toEvalsZeroOne (stmtPair.2 (.column i)).1)
          (MvPolynomial.toEvalsZeroOne (outerTranscriptMultiplicityAt2
            (F := F) (n := n) (M := M) (params := params) tr).1)
          (outerTranscriptXAt2 (F := F) (n := n) (M := M) (params := params) tr)
  | ⟨3, _⟩, tr =>
      stmtPair ∈ (inputRelation F n M).language ∨
        outerBadX (F := F) (n := n) (M := M)
          (MvPolynomial.toEvalsZeroOne (stmtPair.2 .table).1)
          (fun i => MvPolynomial.toEvalsZeroOne (stmtPair.2 (.column i)).1)
          (MvPolynomial.toEvalsZeroOne (outerTranscriptMultiplicityAt3
            (F := F) (n := n) (M := M) (params := params) tr).1)
          (outerTranscriptXAt3 (F := F) (n := n) (M := M) (params := params) tr)
  | ⟨4, _⟩, tr =>
      let table : (Fin n → Fin 2) → F :=
        MvPolynomial.toEvalsZeroOne (stmtPair.2 .table).1
      let columns : Fin M → (Fin n → Fin 2) → F :=
        fun i => MvPolynomial.toEvalsZeroOne (stmtPair.2 (.column i)).1
      let multiplicity : (Fin n → Fin 2) → F :=
        MvPolynomial.toEvalsZeroOne
          (outerTranscriptMultiplicityFull (F := F) (n := n) (M := M) (params := params) tr).1
      let helpers : Fin params.numGroups → (Fin n → Fin 2) → F :=
        fun k => MvPolynomial.toEvalsZeroOne
          (outerTranscriptHelpersFull (F := F) (n := n) (M := M) (params := params) tr k).1
      let x : F := outerTranscriptXFull (F := F) (n := n) (M := M) (params := params) tr
      let batch : BatchingChallenge F n params.numGroups :=
        outerTranscriptBatchFull (F := F) (n := n) (M := M) (params := params) tr
      stmtPair ∈ (inputRelation F n M).language ∨
        outerBadX (F := F) (n := n) (M := M) table columns multiplicity x ∨
          outerBadZ (F := F) (n := n) (M := M) (params := params)
            (params.group) table columns multiplicity helpers x batch.1 ∨
            outerBadBatch (F := F) (n := n) (M := M) (params := params)
              (params.group) table columns multiplicity helpers x batch.1 batch.2

private theorem outerSoundnessState_full_not_lang
    (stmtPair : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : (outerPSpec F n params).FullTranscript)
    (hfalse :
      ¬ outerSoundnessState (F := F) (n := n) (M := M) (params := params)
        stmtPair (Fin.last 4) tr) :
    ({ xChallenge := outerTranscriptXFull (F := F) (n := n) (M := M) (params := params) tr,
       zChallenge :=
        (outerTranscriptBatchFull (F := F) (n := n) (M := M) (params := params) tr).1,
       batchingScalars :=
        (outerTranscriptBatchFull (F := F) (n := n) (M := M) (params := params) tr).2 },
      (fun
        | .input i => stmtPair.2 i
        | .multiplicity =>
            outerTranscriptMultiplicityFull (F := F) (n := n) (M := M) (params := params) tr
        | .helpers =>
            outerTranscriptHelpersFull (F := F) (n := n) (M := M) (params := params) tr))
        ∉ (logupMidRelation F n M params).language := by
  classical
  let table : (Fin n → Fin 2) → F :=
    MvPolynomial.toEvalsZeroOne (stmtPair.2 .table).1
  let columns : Fin M → (Fin n → Fin 2) → F :=
    fun i => MvPolynomial.toEvalsZeroOne (stmtPair.2 (.column i)).1
  let multiplicity : (Fin n → Fin 2) → F :=
    MvPolynomial.toEvalsZeroOne
      (outerTranscriptMultiplicityFull (F := F) (n := n) (M := M) (params := params) tr).1
  let helpers : Fin params.numGroups → (Fin n → Fin 2) → F :=
    fun k => MvPolynomial.toEvalsZeroOne
      (outerTranscriptHelpersFull (F := F) (n := n) (M := M) (params := params) tr k).1
  let x : F := outerTranscriptXFull (F := F) (n := n) (M := M) (params := params) tr
  let batch : BatchingChallenge F n params.numGroups :=
    outerTranscriptBatchFull (F := F) (n := n) (M := M) (params := params) tr
  have hnotLang : stmtPair ∉ (inputRelation F n M).language := by
    intro h
    exact hfalse (by simp [outerSoundnessState, h, table, columns, multiplicity, helpers, x, batch])
  have hnotBadX : ¬ outerBadX (F := F) (n := n) (M := M) table columns multiplicity x := by
    intro hbad
    exact hfalse (by simp [outerSoundnessState, hnotLang, hbad, table, columns, multiplicity,
      helpers, x, batch])
  have hnotBadZ :
      ¬ outerBadZ (F := F) (n := n) (M := M) (params := params)
        (params.group) table columns multiplicity helpers x batch.1 := by
    intro hbad
    exact hfalse (by simp [outerSoundnessState, hnotLang, hnotBadX, hbad, table, columns,
      multiplicity, helpers, x, batch])
  have hnotBadBatch :
      ¬ outerBadBatch (F := F) (n := n) (M := M) (params := params)
        (params.group) table columns multiplicity helpers x batch.1 batch.2 := by
    intro hbad
    exact hfalse (by simp [outerSoundnessState, hnotLang, hnotBadX, hnotBadZ, hbad, table,
      columns, multiplicity, helpers, x, batch])
  have hden : ∀ a : LookupOccur n M, x + lookupOccurValue table columns a ≠ 0 := by
    intro a ha
    exact hnotBadX (Or.inl ⟨a, ha⟩)
  have heval :
      Polynomial.eval x (clearedLookupIdentity table columns multiplicity) ≠ 0 := by
    intro heq
    exact hnotBadX (Or.inr heq)
  have hzGood :
      ∀ k : Fin params.numGroups,
        domainIdentityMLE (F := F) (n := n) (M := M) (params.group) table columns
            multiplicity helpers x k ≠ 0 →
          MvPolynomial.eval batch.1
            (domainIdentityMLE (F := F) (n := n) (M := M) (params.group) table columns
              multiplicity helpers x k) ≠ 0 := by
    intro k hk hzero
    exact hnotBadZ ⟨k, hk, hzero⟩
  have hbatchGood :
      ((∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups, helpers k u) ≠ 0 ∨
          ∃ k : Fin params.numGroups,
            MvPolynomial.eval batch.1
              (domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
                table columns multiplicity helpers x k) ≠ 0) →
        (∑ u : Fin n → Fin 2, ∑ k : Fin params.numGroups, helpers k u) +
          ∑ k : Fin params.numGroups,
            batch.2 k *
              MvPolynomial.eval batch.1
                (domainIdentityMLE (F := F) (n := n) (M := M) (params.group)
                  table columns multiplicity helpers x k) ≠ 0 := by
    intro _
    exact hnotBadBatch
  intro hlang
  rw [Set.mem_language_iff] at hlang
  rcases hlang with ⟨w, hmid⟩
  cases w
  unfold logupMidRelation at hmid
  simp only [Set.mem_setOf_eq] at hmid
  have hne :
      logupOuterSumcheckClaim F n M params
        { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }
        (fun
          | .input i => stmtPair.2 i
          | .multiplicity =>
              outerTranscriptMultiplicityFull (F := F) (n := n) (M := M) (params := params) tr
          | .helpers =>
              outerTranscriptHelpersFull (F := F) (n := n) (M := M) (params := params) tr) ≠ 0 := by
    refine logupOuterSumcheckClaim_ne_zero_of_good_challenges
      (F := F) (n := n) (M := M) (params := params)
      { xChallenge := x, zChallenge := batch.1, batchingScalars := batch.2 }
      (fun
        | .input i => stmtPair.2 i
        | .multiplicity =>
            outerTranscriptMultiplicityFull (F := F) (n := n) (M := M) (params := params) tr
        | .helpers =>
            outerTranscriptHelpersFull (F := F) (n := n) (M := M) (params := params) tr)
      ?_ ?_ ?_ ?_
    · simpa [table, columns, x]
        using hden
    · simpa [table, columns, multiplicity, x]
        using heval
    · simpa [table, columns, multiplicity, helpers, x, batch]
        using hzGood
    · simpa [table, columns, multiplicity, helpers, x, batch]
        using hbatchGood
  exact hne hmid

private theorem outerSoundnessState_empty
    (stmtPair : StmtIn F n M × (∀ i, OStmtIn F n M i)) :
    stmtPair ∈ (inputRelation F n M).language ↔
      outerSoundnessState (F := F) (n := n) (M := M) (params := params)
        stmtPair 0 default := by
  simp [outerSoundnessState]

private theorem outerSoundnessState_next
    (m : Fin 4) (hDir : (outerPSpec F n params).dir m = .P_to_V)
    (stmtPair : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : (outerPSpec F n params).Transcript m.castSucc)
    (hfalse :
      ¬ outerSoundnessState (F := F) (n := n) (M := M) (params := params)
        stmtPair m.castSucc tr)
    (msg : (outerPSpec F n params).«Type» m) :
    ¬ outerSoundnessState (F := F) (n := n) (M := M) (params := params)
        stmtPair m.succ (tr.concat msg) := by
  fin_cases m <;> simp [outerPSpec] at hDir
  · simpa [outerSoundnessState] using hfalse
  · contradiction
  · simpa [outerSoundnessState, outerTranscriptMultiplicityAt2, outerTranscriptMultiplicityAt3,
      outerTranscriptXAt2, outerTranscriptXAt3, ProtocolSpec.Transcript.concat, Fin.snoc]
      using hfalse
  · contradiction

private theorem outerSoundnessState_full_prob_zero
    (stmtPair : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : (outerPSpec F n params).FullTranscript)
    (hfalse :
      ¬ outerSoundnessState (F := F) (n := n) (M := M) (params := params)
        stmtPair (Fin.last 4) tr) :
    Pr[(· ∈ (logupMidRelation F n M params).language) |
      OptionT.mk do
        (simulateQ impl
          (((outerVerifier oSpec F n M params).toVerifier).run stmtPair tr)).run' (← init)] = 0 := by
  classical
  have hnot :=
    outerSoundnessState_full_not_lang (F := F) (n := n) (M := M) (params := params)
      stmtPair tr hfalse
  have hrun :
      (((outerVerifier oSpec F n M params).toVerifier).run stmtPair tr) =
        (pure
          ({ xChallenge := outerTranscriptXFull (F := F) (n := n) (M := M) (params := params) tr,
             zChallenge :=
              (outerTranscriptBatchFull (F := F) (n := n) (M := M) (params := params) tr).1,
             batchingScalars :=
              (outerTranscriptBatchFull (F := F) (n := n) (M := M) (params := params) tr).2 },
            (fun
              | .input i => stmtPair.2 i
              | .multiplicity =>
                  outerTranscriptMultiplicityFull (F := F) (n := n) (M := M)
                    (params := params) tr
              | .helpers =>
                  outerTranscriptHelpersFull (F := F) (n := n) (M := M)
                    (params := params) tr))
          : OptionT (OracleComp oSpec)
              (StmtAfterOuter F n M params ×
                (∀ i, OStmtAfterOuter F n M params i))) := by
    rw [← (OracleVerifier.run_eq_run_verifier
      (stmt := stmtPair.1) (oStmt := stmtPair.2) (transcript := tr)
      (verifier := outerVerifier oSpec F n M params))]
    unfold OracleVerifier.run
    simp only
    rw [outerVerify_simulateQ_eq_soundness
      (oSpec := oSpec) (F := F) (n := n) (M := M) (params := params)
      stmtPair.1 stmtPair.2
      (ProtocolSpec.FullTranscript.messages tr)
      (ProtocolSpec.FullTranscript.challenges tr)]
    simp [outerVerifier, outerChallengeXIdx, outerChallengeBatchIdx,
      outerMultiplicityMessageIdx, outerHelpersMessageIdx, outerTranscriptXFull,
      outerTranscriptBatchFull, outerTranscriptMultiplicityFull, outerTranscriptHelpersFull,
      ProtocolSpec.FullTranscript.challenges, ProtocolSpec.FullTranscript.messages]
    congr
    funext i
    cases i <;> rfl
  rw [hrun]
  let out0 : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i) :=
    ({ xChallenge := outerTranscriptXFull (F := F) (n := n) (M := M) (params := params) tr,
       zChallenge :=
        (outerTranscriptBatchFull (F := F) (n := n) (M := M) (params := params) tr).1,
       batchingScalars :=
        (outerTranscriptBatchFull (F := F) (n := n) (M := M) (params := params) tr).2 },
      (fun
        | .input i => stmtPair.2 i
        | .multiplicity =>
            outerTranscriptMultiplicityFull (F := F) (n := n) (M := M) (params := params) tr
        | .helpers =>
            outerTranscriptHelpersFull (F := F) (n := n) (M := M) (params := params) tr))
  change
    Pr[(· ∈ (logupMidRelation F n M params).language) |
      OptionT.mk do
        (simulateQ impl
          (pure out0 : OptionT (OracleComp oSpec)
            (StmtAfterOuter F n M params ×
              (∀ i, OStmtAfterOuter F n M params i)))).run' (← init)] = 0
  refine probEvent_eq_zero fun out hout houtLang => ?_
  rw [OptionT.mem_support_iff, OptionT.run_mk] at hout
  simp only [support_bind, Set.mem_iUnion] at hout
  rcases hout with ⟨_s, _hs, hout⟩
  have key :
      (simulateQ impl
          (pure out0 : OptionT (OracleComp oSpec)
            (StmtAfterOuter F n M params ×
              (∀ i, OStmtAfterOuter F n M params i)))).run' _s =
        pure (some out0) := by
    change
      (simulateQ impl
          (pure (some out0) : OracleComp oSpec
            (Option (StmtAfterOuter F n M params ×
              (∀ i, OStmtAfterOuter F n M params i))))).run' _s =
        pure (some out0)
    rw [simulateQ_pure]
    change
      Prod.fst <$>
          (pure (some out0) : StateT σ ProbComp
            (Option (StmtAfterOuter F n M params ×
              (∀ i, OStmtAfterOuter F n M params i)))).run _s =
        pure (some out0)
    rw [StateT.run_pure]
    simp [map_pure]
  rw [key] at hout
  simp only [support_pure, Set.mem_singleton_iff] at hout
  have hout_eq : out = out0 := Option.some.inj hout
  subst out
  exact hnot (by simpa [out0] using houtLang)

private noncomputable def outerSoundnessStateFunction :
    ((outerVerifier oSpec F n M params).toVerifier).StateFunction init impl
      (inputRelation F n M).language (logupMidRelation F n M params).language where
  toFun := fun m stmtPair tr =>
    outerSoundnessState (F := F) (n := n) (M := M) (params := params) stmtPair m tr
  toFun_empty := by
    intro stmtPair
    exact outerSoundnessState_empty (F := F) (n := n) (M := M) (params := params) stmtPair
  toFun_next := by
    intro m hDir stmtPair tr hfalse msg
    exact outerSoundnessState_next (F := F) (n := n) (M := M) (params := params)
      m hDir stmtPair tr hfalse msg
  toFun_full := by
    intro stmtPair tr hfalse
    exact outerSoundnessState_full_prob_zero
      (oSpec := oSpec) (F := F) (n := n) (M := M) (params := params)
      (init := init) (impl := impl) stmtPair tr hfalse

private theorem outerChallengeIdx_univ :
    (Finset.univ : Finset (outerPSpec F n params).ChallengeIdx) =
      {outerChallengeXIdx F n M params, outerChallengeBatchIdx F n M params} := by
  ext i
  constructor
  · intro _
    rcases i with ⟨idx, hidx⟩
    fin_cases idx
    · change Direction.P_to_V = Direction.V_to_P at hidx
      cases hidx
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext rfl))
    · change Direction.P_to_V = Direction.V_to_P at hidx
      cases hidx
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr (Subtype.ext rfl)))
  · intro _
    exact Finset.mem_univ i

/-- Protocol-level bridge for the outer phase: the local algebraic ingredients above imply the
conservative scan-free outer soundness bound used by `logupOuterSoundnessError`. -/
private theorem logup_outer_soundness_from_local_algebra
    (hcard : Fintype.card (Fin n → Fin 2) < Fintype.card F)
    (hClearedNonzero :
      ∀ (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
        (multiplicity : (Fin n → Fin 2) → F),
        ((stmt, oStmt), ()) ∉ inputRelation F n M →
          clearedLookupIdentity
              (MvPolynomial.toEvalsZeroOne (oStmt .table).1)
              (fun i => MvPolynomial.toEvalsZeroOne (oStmt (.column i)).1)
              multiplicity ≠ 0)
    (hClearedDegree :
      ∀ (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
        (multiplicity : (Fin n → Fin 2) → F),
        (clearedLookupIdentity table columns multiplicity).natDegree ≤
          (M + 1) * Fintype.card (Fin n → Fin 2) - 1)
    (hBadRoots :
      ∀ (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
        (multiplicity : (Fin n → Fin 2) → F),
        clearedLookupIdentity table columns multiplicity ≠ 0 →
          (Finset.univ.filter fun x : F =>
            (∀ u : Fin n → Fin 2, x + table u ≠ 0) ∧
              Polynomial.eval x (clearedLookupIdentity table columns multiplicity) = 0).card ≤
            (M + 1) * Fintype.card (Fin n → Fin 2) - 1)
    (hBatch :
      ∀ (K : ℕ) (c₀ : F) (c : Fin K → F),
        c₀ ≠ 0 ∨ (∃ k, c k ≠ 0) →
          Pr[fun lam : Fin K → F => c₀ + ∑ k : Fin K, lam k * c k = 0 |
              $ᵗ (Fin K → F)] ≤
            ((1 : ℕ) : ENNReal) / (Fintype.card F : ENNReal)) :
    (outerVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language (logupMidRelation F n M params).language
      (logupOuterSoundnessError F n M params) := by
  classical
  let xErr : ℝ≥0 :=
    ((((M + 1) * Fintype.card (Fin n → Fin 2) : ℕ) : ℝ≥0) /
        (Fintype.card F : ℝ≥0)) +
      ((((M + 1) * Fintype.card (Fin n → Fin 2) - 1 : ℕ) : ℝ≥0) /
        (Fintype.card F : ℝ≥0))
  let batchErr : ℝ≥0 :=
    (((params.numGroups * n : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)) +
      ((1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
  let rbrErr : (outerPSpec F n params).ChallengeIdx → ℝ≥0 :=
    fun i => if i.1 = (outerChallengeXIdx F n M params).1 then xErr else batchErr
  have hrbr :
      ((outerVerifier oSpec F n M params).toVerifier).rbrSoundness init impl
        (inputRelation F n M).language (logupMidRelation F n M params).language
        rbrErr := by
    refine ⟨outerSoundnessStateFunction (oSpec := oSpec) (F := F) (n := n) (M := M)
      (params := params) (init := init) (impl := impl), ?_⟩
    intro stmtPair hstmt WitIn WitOut witIn prover i
    have hi_mem :
        i ∈ ({outerChallengeXIdx F n M params,
          outerChallengeBatchIdx F n M params} :
            Finset (outerPSpec F n params).ChallengeIdx) := by
      rw [← outerChallengeIdx_univ (F := F) (n := n) (M := M) (params := params)]
      exact Finset.mem_univ i
    rw [Finset.mem_insert, Finset.mem_singleton] at hi_mem
    rcases hi_mem with hi | hi
    · subst i
      let table : (Fin n → Fin 2) → F :=
        MvPolynomial.toEvalsZeroOne (stmtPair.2 .table).1
      let columns : Fin M → (Fin n → Fin 2) → F :=
        fun j => MvPolynomial.toEvalsZeroOne (stmtPair.2 (.column j)).1
      let BadXPair : (outerPSpec F n params).Transcript (1 : Fin 5) × F → Prop :=
        fun p =>
          outerBadX (F := F) (n := n) (M := M) table columns
            (MvPolynomial.toEvalsZeroOne
              (outerTranscriptMultiplicity (F := F) (n := n) (M := M)
                (params := params) p.1).1)
            p.2
      refine le_trans (probEvent_mono'' (q := BadXPair) ?_) ?_
      · intro p hp
        rcases hp with ⟨hfalse, htrue⟩
        have hnotLang' : ¬ ∃ w, (stmtPair, w) ∈ inputRelation F n M := by
          simpa [Set.mem_language_iff] using hstmt
        have htrue' :
            (∃ w, (stmtPair, w) ∈ inputRelation F n M) ∨
              outerBadX (F := F) (n := n) (M := M) table columns
                (MvPolynomial.toEvalsZeroOne
                  (outerTranscriptMultiplicity (F := F) (n := n) (M := M)
                    (params := params) p.1).1)
                p.2 := by
          simpa [BadXPair, outerSoundnessStateFunction, outerSoundnessState,
            outerChallengeXIdx, outerTranscriptMultiplicity, outerTranscriptMultiplicityAt2,
            outerTranscriptXAt2, ProtocolSpec.Transcript.concat, Fin.snoc, table, columns]
            using htrue
        exact htrue'.resolve_left hnotLang'
      · refine probEvent_bind_le_of_forall_le ?_
        intro s _hs
        rw [simulateQ_bind, StateT.run'_bind']
        refine probEvent_bind_le_of_forall_le ?_
        intro xs _hxs
        rcases xs with ⟨a, s'⟩
        rcases a with ⟨tr, _proverState⟩
        have hnotRel : ((stmtPair.1, stmtPair.2), ()) ∉ inputRelation F n M := by
          intro hrel
          exact hstmt (by
            rw [Set.mem_language_iff]
            exact ⟨(), hrel⟩)
        have hpoly :
            clearedLookupIdentity table columns
                (MvPolynomial.toEvalsZeroOne
                  (outerTranscriptMultiplicity (F := F) (n := n) (M := M)
                    (params := params) tr).1) ≠ 0 := by
          simpa [table, columns] using
            hClearedNonzero stmtPair.1 stmtPair.2
              (MvPolynomial.toEvalsZeroOne
                (outerTranscriptMultiplicity (F := F) (n := n) (M := M)
                  (params := params) tr).1)
              hnotRel
        have hUniform :
            Pr[fun x : F => BadXPair (tr, x) | $ᵗ F] ≤
              (xErr : ENNReal) := by
          simpa [BadXPair, outerBadX, xErr, table, columns] using
            clearedLookupIdentity_bad_x_prob_le
              (F := F) (n := n) (M := M) table columns
              (MvPolynomial.toEvalsZeroOne
                (outerTranscriptMultiplicity (F := F) (n := n) (M := M)
                  (params := params) tr).1)
              hpoly
        change
          Pr[BadXPair |
            (simulateQ
              (impl.addLift ProtocolSpec.challengeQueryImpl :
                QueryImpl
                  (oSpec + [(outerPSpec F n params).Challenge]ₒ'
                    ProtocolSpec.challengeOracleInterface)
                  (StateT σ ProbComp))
              (do
                let challenge ←
                  ((outerPSpec F n params).getChallenge (outerChallengeXIdx F n M params)).liftComp
                    (oSpec + [(outerPSpec F n params).Challenge]ₒ'
                      ProtocolSpec.challengeOracleInterface)
                pure (tr, challenge))).run' s'] ≤
            ↑(rbrErr (outerChallengeXIdx F n M params))
        have hchallenge :
            (simulateQ
              (impl.addLift ProtocolSpec.challengeQueryImpl :
                QueryImpl
                  (oSpec + [(outerPSpec F n params).Challenge]ₒ'
                    ProtocolSpec.challengeOracleInterface)
                  (StateT σ ProbComp))
              (do
                let challenge ←
                  ((outerPSpec F n params).getChallenge (outerChallengeXIdx F n M params)).liftComp
                    (oSpec + [(outerPSpec F n params).Challenge]ₒ'
                      ProtocolSpec.challengeOracleInterface)
                pure (tr, challenge))).run' s' =
              (($ᵗ F) >>= (pure ∘ fun x : F => (tr, x))) := by
          simp only [simulateQ_bind, ProtocolSpec.getChallenge, QueryImpl.addLift_def,
            QueryImpl.simulateQ_add_liftComp_right, HasQuery.instOfMonadLift_query,
            outerChallengeXIdx, StateT.run'_bind', simulateQ_pure, StateT.run'_pure']
          let qIn : ([(outerPSpec F n params).Challenge]ₒ'
              ProtocolSpec.challengeOracleInterface).Domain :=
            ⟨outerChallengeXIdx F n M params, ()⟩
          have hq :
              simulateQ
                (QueryImpl.liftTarget (StateT σ ProbComp)
                  (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params)))
                (liftM (OracleSpec.query qIn) :
                  OracleComp ([(outerPSpec F n params).Challenge]ₒ'
                    ProtocolSpec.challengeOracleInterface) F) =
              (liftM ($ᵗ F) : StateT σ ProbComp F) := by
            rw [simulateQ_query]
            simp [qIn, ProtocolSpec.challengeQueryImpl, QueryImpl.liftTarget_apply,
              outerChallengeXIdx]
            change id <$> (liftM (($ᵗ F) : ProbComp F) : StateT σ ProbComp F) =
              (liftM (($ᵗ F) : ProbComp F) : StateT σ ProbComp F)
            simp
          change
            (do
              let x ←
                (simulateQ
                  (QueryImpl.liftTarget (StateT σ ProbComp)
                    (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params)))
                  (liftM (OracleSpec.query qIn) :
                    OracleComp ([(outerPSpec F n params).Challenge]ₒ'
                      ProtocolSpec.challengeOracleInterface) F)).run s'
              pure (tr, x.1)) =
                (($ᵗ F) >>= (pure ∘ fun x : F => (tr, x)))
          rw [hq]
          simp [StateT.run_liftM, bind_assoc, map_eq_bind_pure_comp]
        rw [hchallenge]
        calc
          Pr[BadXPair | (($ᵗ F) >>= (pure ∘ fun x : F => (tr, x)))]
              = Pr[BadXPair ∘ (fun x : F => (tr, x)) | $ᵗ F] := by
                exact probEvent_bind_pure_comp (($ᵗ F) : ProbComp F)
                  (fun x : F => (tr, x)) BadXPair
          _ ≤ ↑(rbrErr (outerChallengeXIdx F n M params)) := by
                simpa [Function.comp_def, rbrErr, outerChallengeXIdx] using hUniform
    · subst i
      letI : Inhabited F := ⟨0⟩
      letI : SampleableType (BatchingChallenge F n params.numGroups) := by
        change SampleableType ((Fin n → F) × (Fin params.numGroups → F))
        infer_instance
      let table : (Fin n → Fin 2) → F :=
        MvPolynomial.toEvalsZeroOne (stmtPair.2 .table).1
      let columns : Fin M → (Fin n → Fin 2) → F :=
        fun j => MvPolynomial.toEvalsZeroOne (stmtPair.2 (.column j)).1
      let BadBatchPair :
          (outerPSpec F n params).Transcript (3 : Fin 5) ×
            BatchingChallenge F n params.numGroups → Prop :=
        fun p =>
          ¬ outerSoundnessState (F := F) (n := n) (M := M) (params := params)
              stmtPair (3 : Fin 5) p.1 ∧
            (let multiplicity : (Fin n → Fin 2) → F :=
                MvPolynomial.toEvalsZeroOne
                  (outerTranscriptMultiplicityAt3 (F := F) (n := n) (M := M)
                    (params := params) p.1).1
             let helpers : Fin params.numGroups → (Fin n → Fin 2) → F :=
                fun k => MvPolynomial.toEvalsZeroOne
                  (outerTranscriptHelpersAt3 (F := F) (n := n) (M := M)
                    (params := params) p.1 k).1
             let x : F :=
                outerTranscriptXAt3 (F := F) (n := n) (M := M) (params := params) p.1
             outerBadZ (F := F) (n := n) (M := M) (params := params)
                (params.group) table columns multiplicity helpers x p.2.1 ∨
              outerBadBatch (F := F) (n := n) (M := M) (params := params)
                (params.group) table columns multiplicity helpers x p.2.1 p.2.2)
      refine le_trans (probEvent_mono'' (q := BadBatchPair) ?_) ?_
      · intro p hp
        rcases hp with ⟨hfalse, htrue⟩
        refine ⟨?_, ?_⟩
        · simpa [outerSoundnessStateFunction, outerChallengeBatchIdx] using hfalse
        · let multiplicity : (Fin n → Fin 2) → F :=
            MvPolynomial.toEvalsZeroOne
              (outerTranscriptMultiplicityAt3 (F := F) (n := n) (M := M)
                (params := params) p.1).1
          let helpers : Fin params.numGroups → (Fin n → Fin 2) → F :=
            fun k => MvPolynomial.toEvalsZeroOne
              (outerTranscriptHelpersAt3 (F := F) (n := n) (M := M)
                (params := params) p.1 k).1
          let x : F :=
            outerTranscriptXAt3 (F := F) (n := n) (M := M) (params := params) p.1
          have hnotLang : ¬ ∃ w, (stmtPair, w) ∈ inputRelation F n M := by
            simpa [Set.mem_language_iff] using hstmt
          have hnotBadX :
              ¬ outerBadX (F := F) (n := n) (M := M)
                table columns multiplicity x := by
            intro hbad
            exact hfalse (by
              simpa [outerSoundnessStateFunction, outerSoundnessState,
                outerChallengeBatchIdx, outerTranscriptMultiplicityAt3, outerTranscriptXAt3,
                table, columns, multiplicity, x] using
                (Or.inr hbad :
                  stmtPair ∈ (inputRelation F n M).language ∨
                    outerBadX (F := F) (n := n) (M := M)
                      table columns multiplicity x))
          have htrue' :
              (∃ w, (stmtPair, w) ∈ inputRelation F n M) ∨
                outerBadX (F := F) (n := n) (M := M)
                  table columns multiplicity x ∨
                  outerBadZ (F := F) (n := n) (M := M) (params := params)
                    (params.group) table columns multiplicity helpers x p.2.1 ∨
                    outerBadBatch (F := F) (n := n) (M := M) (params := params)
                      (params.group) table columns multiplicity helpers x p.2.1 p.2.2 := by
            simpa [outerSoundnessStateFunction, outerSoundnessState, outerChallengeBatchIdx,
              outerTranscriptMultiplicityAt3, outerTranscriptXAt3, outerTranscriptHelpersAt3,
              outerTranscriptMultiplicityFull, outerTranscriptXFull, outerTranscriptHelpersFull,
              outerTranscriptBatchFull, ProtocolSpec.Transcript.concat, Fin.snoc,
              table, columns, multiplicity, helpers, x] using htrue
          rcases htrue' with hlang | hbadx | hbadz | hbadBatch
          · exact False.elim (hnotLang hlang)
          · exact False.elim (hnotBadX hbadx)
          · exact Or.inl hbadz
          · exact Or.inr hbadBatch
      · refine probEvent_bind_le_of_forall_le ?_
        intro s _hs
        rw [simulateQ_bind, StateT.run'_bind']
        refine probEvent_bind_le_of_forall_le ?_
        intro xs _hxs
        rcases xs with ⟨a, s'⟩
        rcases a with ⟨tr, _proverState⟩
        let multiplicity : (Fin n → Fin 2) → F :=
          MvPolynomial.toEvalsZeroOne
            (outerTranscriptMultiplicityAt3 (F := F) (n := n) (M := M)
              (params := params) tr).1
        let helpers : Fin params.numGroups → (Fin n → Fin 2) → F :=
          fun k => MvPolynomial.toEvalsZeroOne
            (outerTranscriptHelpersAt3 (F := F) (n := n) (M := M)
              (params := params) tr k).1
        let x : F :=
          outerTranscriptXAt3 (F := F) (n := n) (M := M) (params := params) tr
        have hUniform :
            Pr[fun batch : BatchingChallenge F n params.numGroups =>
                BadBatchPair (tr, batch) | $ᵗ (BatchingChallenge F n params.numGroups)] ≤
              (batchErr : ENNReal) := by
          by_cases hfalse :
              ¬ outerSoundnessState (F := F) (n := n) (M := M) (params := params)
                stmtPair (3 : Fin 5) tr
          · letI : Inhabited F := ⟨0⟩
            have hnotBadX :
                ¬ outerBadX (F := F) (n := n) (M := M)
                  table columns multiplicity x := by
              intro hbad
              exact hfalse (by
                simpa [outerSoundnessState, outerTranscriptMultiplicityAt3,
                  outerTranscriptXAt3, table, columns, multiplicity, x] using
                  (Or.inr hbad :
                    stmtPair ∈ (inputRelation F n M).language ∨
                      outerBadX (F := F) (n := n) (M := M)
                        table columns multiplicity x))
            have hden :
                ∀ a : LookupOccur n M, x + lookupOccurValue table columns a ≠ 0 := by
              intro a ha
              exact hnotBadX (Or.inl ⟨a, ha⟩)
            have heval :
                Polynomial.eval x (clearedLookupIdentity table columns multiplicity) ≠ 0 := by
              intro heq
              exact hnotBadX (Or.inr heq)
            have hBatchBound :
                Pr[fun batch : BatchingChallenge F n params.numGroups =>
                    outerBadZ (F := F) (n := n) (M := M) (params := params)
                        (params.group) table columns multiplicity helpers x batch.1 ∨
                      outerBadBatch (F := F) (n := n) (M := M) (params := params)
                        (params.group) table columns multiplicity helpers x batch.1 batch.2 |
                    $ᵗ (BatchingChallenge F n params.numGroups)] ≤
                  (batchErr : ENNReal) := by
              simpa [batchErr, Nat.cast_mul, mul_div_assoc] using
                outerBatchChallenge_bad_prob_le
                  (F := F) (n := n) (M := M) (params := params)
                  hBatch (params.group)
                  (sum_protocolGroups_soundness (F := F) (M := M) params)
                  table columns multiplicity helpers x hden heval
            refine le_trans (probEvent_mono'' ?_) hBatchBound
            intro batch hbad
            simpa [BadBatchPair, hfalse, multiplicity, helpers, x] using hbad
          · have hfalseEvent :
                (fun batch : BatchingChallenge F n params.numGroups =>
                    BadBatchPair (tr, batch)) = fun _ => False := by
              funext batch
              simp [BadBatchPair, hfalse, multiplicity, helpers, x]
            rw [hfalseEvent]
            simp [batchErr]
        change
          Pr[BadBatchPair |
            (simulateQ
              (impl.addLift ProtocolSpec.challengeQueryImpl :
                QueryImpl
                  (oSpec + [(outerPSpec F n params).Challenge]ₒ'
                    ProtocolSpec.challengeOracleInterface)
                  (StateT σ ProbComp))
              (do
                let challenge ←
                  ((outerPSpec F n params).getChallenge
                    (outerChallengeBatchIdx F n M params)).liftComp
                    (oSpec + [(outerPSpec F n params).Challenge]ₒ'
                      ProtocolSpec.challengeOracleInterface)
                pure (tr, challenge))).run' s'] ≤
            ↑(rbrErr (outerChallengeBatchIdx F n M params))
        have hchallenge :
            (simulateQ
              (impl.addLift ProtocolSpec.challengeQueryImpl :
                QueryImpl
                  (oSpec + [(outerPSpec F n params).Challenge]ₒ'
                    ProtocolSpec.challengeOracleInterface)
                  (StateT σ ProbComp))
              (do
                let challenge ←
                  ((outerPSpec F n params).getChallenge
                    (outerChallengeBatchIdx F n M params)).liftComp
                    (oSpec + [(outerPSpec F n params).Challenge]ₒ'
                      ProtocolSpec.challengeOracleInterface)
                pure (tr, challenge))).run' s' =
              (($ᵗ (BatchingChallenge F n params.numGroups)) >>=
                (pure ∘ fun batch : BatchingChallenge F n params.numGroups => (tr, batch))) := by
          simp only [simulateQ_bind, ProtocolSpec.getChallenge, QueryImpl.addLift_def,
            QueryImpl.simulateQ_add_liftComp_right, HasQuery.instOfMonadLift_query,
            outerChallengeBatchIdx, StateT.run'_bind', simulateQ_pure, StateT.run'_pure']
          let qIn : ([(outerPSpec F n params).Challenge]ₒ'
              ProtocolSpec.challengeOracleInterface).Domain :=
            ⟨outerChallengeBatchIdx F n M params, ()⟩
          have hq :
              simulateQ
                (QueryImpl.liftTarget (StateT σ ProbComp)
                  (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params)))
                (liftM (OracleSpec.query qIn) :
                  OracleComp ([(outerPSpec F n params).Challenge]ₒ'
                    ProtocolSpec.challengeOracleInterface)
                    (BatchingChallenge F n params.numGroups)) =
              (liftM ($ᵗ (BatchingChallenge F n params.numGroups)) :
                StateT σ ProbComp (BatchingChallenge F n params.numGroups)) := by
            rw [simulateQ_query]
            simp [qIn, ProtocolSpec.challengeQueryImpl, QueryImpl.liftTarget_apply,
              outerChallengeBatchIdx]
            change id <$> (liftM (($ᵗ (BatchingChallenge F n params.numGroups)) :
                ProbComp (BatchingChallenge F n params.numGroups)) :
                StateT σ ProbComp (BatchingChallenge F n params.numGroups)) =
              (liftM (($ᵗ (BatchingChallenge F n params.numGroups)) :
                ProbComp (BatchingChallenge F n params.numGroups)) :
                StateT σ ProbComp (BatchingChallenge F n params.numGroups))
            simp
          change
            (do
              let batch ←
                (simulateQ
                  (QueryImpl.liftTarget (StateT σ ProbComp)
                    (ProtocolSpec.challengeQueryImpl (pSpec := outerPSpec F n params)))
                  (liftM (OracleSpec.query qIn) :
                    OracleComp ([(outerPSpec F n params).Challenge]ₒ'
                      ProtocolSpec.challengeOracleInterface)
                      (BatchingChallenge F n params.numGroups))).run s'
              pure (tr, batch.1)) =
                (($ᵗ (BatchingChallenge F n params.numGroups)) >>=
                  (pure ∘ fun batch : BatchingChallenge F n params.numGroups => (tr, batch)))
          rw [hq]
          simp [StateT.run_liftM, bind_assoc, map_eq_bind_pure_comp]
        rw [hchallenge]
        calc
          Pr[BadBatchPair |
              (($ᵗ (BatchingChallenge F n params.numGroups)) >>=
                (pure ∘ fun batch : BatchingChallenge F n params.numGroups => (tr, batch)))]
              =
            Pr[BadBatchPair ∘
                (fun batch : BatchingChallenge F n params.numGroups => (tr, batch)) |
              $ᵗ (BatchingChallenge F n params.numGroups)] := by
                exact probEvent_bind_pure_comp
                  (($ᵗ (BatchingChallenge F n params.numGroups)) :
                    ProbComp (BatchingChallenge F n params.numGroups))
                  (fun batch : BatchingChallenge F n params.numGroups => (tr, batch))
                  BadBatchPair
          _ ≤ ↑(rbrErr (outerChallengeBatchIdx F n M params)) := by
                simpa [Function.comp_def, rbrErr, outerChallengeBatchIdx] using hUniform
  have hsound :=
    Verifier.rbrSoundness_implies_soundness
      (init := init) (impl := impl)
      ((inputRelation F n M).language)
      ((logupMidRelation F n M params).language)
      ((outerVerifier oSpec F n M params).toVerifier)
      rbrErr hrbr
  unfold OracleVerifier.soundness
  convert hsound using 1
  have hsum : (∑ i : (outerPSpec F n params).ChallengeIdx, rbrErr i) = xErr + batchErr := by
    rw [show (Finset.univ : Finset (outerPSpec F n params).ChallengeIdx) =
      {outerChallengeXIdx F n M params, outerChallengeBatchIdx F n M params} from
        outerChallengeIdx_univ (F := F) (n := n) (M := M) (params := params)]
    rw [Finset.sum_insert]
    · rw [Finset.sum_singleton]
      have hne :
          ((outerChallengeBatchIdx F n M params).1 :
            Fin 4) ≠ (outerChallengeXIdx F n M params).1 := by
        simp [outerChallengeXIdx, outerChallengeBatchIdx]
      simp [rbrErr, outerChallengeXIdx, outerChallengeBatchIdx]
    · intro hx
      rw [Finset.mem_singleton] at hx
      have hval := congrArg Subtype.val hx
      norm_num [outerChallengeXIdx, outerChallengeBatchIdx] at hval
      omega
  rw [hsum]
  simp [xErr, batchErr, logupOuterSoundnessError, add_assoc]

/-! ## Phase soundness lemmas

One soundness statement per phase, against the intermediate languages handed between phases. -/

omit [Fintype F] [DecidableEq F] [SampleableType F] in
private theorem sum_piFinset_map_univ_eq_sum_hypercube
    (D : Fin 2 ↪ F) (f : (Fin n → F) → F) :
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
      ∑ u : (Fin n → Fin 2), f (fun j => D (u j)) := by
  let e : (Fin n → Fin 2) ↪ (Fin n → F) := Function.Embedding.arrowCongrRight D
  change (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
    ∑ u : (Fin n → Fin 2), f (e u)
  rw [← Finset.sum_map]
  congr 1
  ext x
  simp only [Fintype.mem_piFinset, Finset.mem_map, Finset.mem_univ, true_and, true_imp_iff]
  constructor
  · intro hx
    choose y hy using hx
    refine ⟨y, ?_⟩
    funext i
    exact hy i
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩

private theorem logupSumcheckRelationInput_iff
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i} :
    logupSumcheckRelationInput F n M params stmt oStmt ↔
      logupOuterSumcheckClaim F n M params stmt oStmt = 0 := by
  unfold logupSumcheckRelationInput Sumcheck.Spec.relationRound
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero, logupInitialSumcheckStatement,
    Set.mem_setOf_eq, Fin.elim0_append, logupSumcheckOracleStmt]
  change
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map (booleanDomain F),
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val) = 0 ↔
      logupOuterSumcheckClaim F n M params stmt oStmt = 0
  rw [sum_piFinset_map_univ_eq_sum_hypercube
    (F := F) (n := n) (D := booleanDomain F)
    (f := fun x =>
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val)]
  change
    (∑ u : (Fin n → Fin 2),
        MvPolynomial.eval (fun i => (u i : F))
          (logupSumcheckPolynomial F n M params stmt oStmt).val) = 0 ↔
      logupOuterSumcheckClaim F n M params stmt oStmt = 0
  have hsum :
      (∑ u : (Fin n → Fin 2),
          MvPolynomial.eval (fun i => (u i : F))
            (logupSumcheckPolynomial F n M params stmt oStmt).val) =
        logupOuterSumcheckClaim F n M params stmt oStmt := by
    rw [logupOuterSumcheckClaim]
    apply Finset.sum_congr rfl
    intro u _
    simp only [booleanDomain, logupSumcheckPolynomial]
  rw [hsum]

private theorem seqCompose_verifier_preserves {ι : Type} {oSpec : OracleSpec ι} (m : ℕ) :
    ∀ {Stmt : Fin (m + 1) → Type} {O : Type}
      {rounds : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (rounds i)}
      (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
      (proj : (i : Fin (m + 1)) → Stmt i → O),
      (∀ (i : Fin m) (stmt : Stmt i.castSucc) (out : Stmt i.succ)
          (tr : (pSpec i).FullTranscript),
        out ∈ support ((V i).run stmt tr) →
          proj i.succ out = proj i.castSucc stmt) →
      ∀ (stmt : Stmt 0) (out : Stmt (Fin.last m))
        (tr : (ProtocolSpec.seqCompose pSpec).FullTranscript),
        out ∈ support ((Verifier.seqCompose Stmt V).run stmt tr) →
        proj (Fin.last m) out = proj 0 stmt := by
  induction m with
  | zero =>
      intro Stmt O rounds pSpec V proj _hV stmt out tr h
      rw [Verifier.seqCompose_zero] at h
      simp only [Verifier.run, Verifier.id] at h
      cases h
      rfl
  | succ m ih =>
      intro Stmt O rounds pSpec V proj hV stmt out tr h
      let tailSpec : ProtocolSpec (Fin.vsum fun i : Fin m => rounds (Fin.succ i)) :=
        ProtocolSpec.seqCompose (fun i : Fin m => pSpec (Fin.succ i))
      let tail : Verifier oSpec (Stmt (Fin.succ 0)) (Stmt (Fin.last (m + 1))) tailSpec :=
        Verifier.seqCompose (fun i => Stmt i.succ) (fun i => V (Fin.succ i))
      let trApp : ((pSpec 0) ++ₚ tailSpec).FullTranscript := tr
      have h' : out ∈ support (((do
          let stmt₂ ← (V 0).run stmt trApp.fst
          let stmt₃ ← tail.run stmt₂ trApp.snd
          return stmt₃) : OptionT (OracleComp oSpec) (Stmt (Fin.last (m + 1))))) := by
        change out ∈ support ((Verifier.append (V 0) tail).run stmt trApp) at h
        rw [Verifier.append_run] at h
        exact h
      rw [mem_support_bind_iff] at h'
      rcases h' with ⟨stmt₂, h₁, hrest⟩
      rw [mem_support_bind_iff] at hrest
      rcases hrest with ⟨stmt₃, h₂, hpure⟩
      rw [support_pure, Set.mem_singleton_iff] at hpure
      cases hpure
      calc
        proj (Fin.last (m + 1)) out = proj (Fin.succ (Fin.last m)) out := rfl
        _ = proj (Fin.succ (0 : Fin (m + 1))) stmt₂ := by
          exact ih
            (V := fun i => V (Fin.succ i))
            (proj := fun i => proj (Fin.succ i))
            (fun i stmt out tr h => hV (Fin.succ i) stmt out tr h)
            stmt₂ out trApp.snd h₂
        _ = proj 0 stmt := hV 0 stmt stmt₂ trApp.fst h₁

omit [Fintype F] [SampleableType F] in
private theorem sumcheckSingleRoundVerifier_preserves_oracleStmt
    {deg : ℕ} (D : Fin 2 ↪ F) (i : Fin n)
    {stmt : Sumcheck.Spec.StatementRound F n i.castSucc ×
      (∀ j, Sumcheck.Spec.OracleStatement F n deg j)}
    {out : Sumcheck.Spec.StatementRound F n i.succ ×
      (∀ j, Sumcheck.Spec.OracleStatement F n deg j)}
    {tr : (Sumcheck.Spec.SingleRound.pSpec F deg).FullTranscript}
    (h : out ∈ support ((Sumcheck.Spec.SingleRound.verifier F n deg D oSpec i).run stmt tr)) :
    out.2 = stmt.2 := by
  rw [Sumcheck.Spec.SingleRound.verifier, Verifier.run, Verifier.liftContext] at h
  rw [mem_support_bind_iff] at h
  rcases h with ⟨innerOut, _hInner, hOut⟩
  rw [support_pure, Set.mem_singleton_iff] at hOut
  cases hOut
  rcases stmt with ⟨⟨_oldTarget, _challenges⟩, oStmt⟩
  rcases innerOut with ⟨⟨_newTarget, _chal⟩, _oStmt'⟩
  rfl

private theorem sumcheckVerifier_preserves_oracleStmt
    {deg : ℕ} (D : Fin 2 ↪ F)
    {stmt : Sumcheck.Spec.StatementRound F n 0 ×
      (∀ j, Sumcheck.Spec.OracleStatement F n deg j)}
    {out : Sumcheck.Spec.StatementRound F n (Fin.last n) ×
      (∀ j, Sumcheck.Spec.OracleStatement F n deg j)}
    {tr : (Sumcheck.Spec.pSpec F deg n).FullTranscript}
    (h : out ∈ support ((Sumcheck.Spec.verifier F deg D n oSpec).run stmt tr)) :
    out.2 = stmt.2 := by
  refine @seqCompose_verifier_preserves ι oSpec n
    (Stmt := fun i => Sumcheck.Spec.StatementRound F n i ×
      (∀ j, Sumcheck.Spec.OracleStatement F n deg j))
    (O := ∀ j, Sumcheck.Spec.OracleStatement F n deg j)
    (rounds := fun _ => 2)
    (pSpec := fun _ => Sumcheck.Spec.SingleRound.pSpec F deg)
    (V := fun i => Sumcheck.Spec.SingleRound.verifier F n deg D oSpec i)
    (proj := fun _ stmt => stmt.2) ?_ stmt out tr ?_
  · intro i stmt out tr h
    exact sumcheckSingleRoundVerifier_preserves_oracleStmt
      (oSpec := oSpec) (F := F) (n := n) D i h
  · exact h

omit [Fintype F] in
private theorem sumcheckSingleRoundOracleReduction_toReduction_verifier_eq_verifier
    {deg : ℕ} (D : Fin 2 ↪ F) (i : Fin n) :
    ((Sumcheck.Spec.SingleRound.oracleReduction F n deg D oSpec i).toReduction).verifier =
      Sumcheck.Spec.SingleRound.verifier F n deg D oSpec i := by
  rw [Sumcheck.Spec.SingleRound.oracleReduction]
  rw [OracleReduction.liftContext_toReduction_comm]
  rw [Sumcheck.Spec.SingleRound.Simple.oracleReduction_eq_reduction]
  rfl

private theorem sumcheckOracleReductionVerifier_toVerifier_eq_verifier
    {deg : ℕ} (D : Fin 2 ↪ F) :
    (Sumcheck.Spec.oracleReduction F deg D n oSpec).verifier.toVerifier =
      Sumcheck.Spec.verifier F deg D n oSpec := by
  have h := congrArg Reduction.verifier
    (OracleReduction.seqCompose_toReduction
      (oSpec := oSpec)
      (Stmt := Sumcheck.Spec.StatementRound F n)
      (OStmt := fun _ => Sumcheck.Spec.OracleStatement F n deg)
      (Wit := fun _ => Unit)
      (pSpec := fun _ => Sumcheck.Spec.SingleRound.pSpec F deg)
      (R := Sumcheck.Spec.SingleRound.oracleReduction F n deg D oSpec))
  change (Sumcheck.Spec.oracleReduction F deg D n oSpec).verifier.toVerifier =
      (Reduction.seqCompose
        (fun i => Sumcheck.Spec.StatementRound F n i ×
          (∀ j, Sumcheck.Spec.OracleStatement F n deg j))
        (fun _ => Unit)
        (fun i => (Sumcheck.Spec.SingleRound.oracleReduction F n deg D oSpec i).toReduction)
      ).verifier at h
  rw [h]
  change
      Verifier.seqCompose
        (fun i => Sumcheck.Spec.StatementRound F n i ×
          (∀ j, Sumcheck.Spec.OracleStatement F n deg j))
        (fun i =>
          ((Sumcheck.Spec.SingleRound.oracleReduction F n deg D oSpec i).toReduction).verifier) =
      Sumcheck.Spec.verifier F deg D n oSpec
  change
      Verifier.seqCompose
        (fun i => Sumcheck.Spec.StatementRound F n i ×
          (∀ j, Sumcheck.Spec.OracleStatement F n deg j))
        (fun i =>
          ((Sumcheck.Spec.SingleRound.oracleReduction F n deg D oSpec i).toReduction).verifier) =
      Verifier.seqCompose
        (fun i => Sumcheck.Spec.StatementRound F n i ×
          (∀ j, Sumcheck.Spec.OracleStatement F n deg j))
        (Sumcheck.Spec.SingleRound.verifier F n deg D oSpec)
  congr
  funext i
  exact sumcheckSingleRoundOracleReduction_toReduction_verifier_eq_verifier
    (oSpec := oSpec) (F := F) (n := n) D i

private theorem sumcheckVerifier_compat_oracleStmt
    {outerStmt : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i)}
    {innerStmtOut : Sumcheck.Spec.StatementRound F n (Fin.last n) ×
      (∀ i, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) i)}
    (hCompat :
      Verifier.compatStatement (logupSumcheckContextLens F n M params).stmt
        (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.toVerifier
        outerStmt innerStmtOut) :
    innerStmtOut.2 = logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2 := by
  rcases hCompat with ⟨tr, htr⟩
  have hrun : innerStmtOut ∈ support
      ((Sumcheck.Spec.verifier F (logupSumcheckDegree M params) (booleanDomain F) n oSpec).run
        (logupInitialSumcheckStatement F n,
          logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) tr) := by
    rw [logupConcreteSumcheckOracleReduction,
      sumcheckOracleReductionVerifier_toVerifier_eq_verifier] at htr
    change innerStmtOut ∈ support
      ((Sumcheck.Spec.verifier F (logupSumcheckDegree M params) (booleanDomain F) n oSpec).run
        (logupInitialSumcheckStatement F n,
          logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) tr) at htr
    exact htr
  exact sumcheckVerifier_preserves_oracleStmt (oSpec := oSpec) (F := F) (n := n)
    (D := booleanDomain F) hrun

private instance logupSumcheckLensSound :
    (logupSumcheckContextLens F n M params).stmt.IsSound
      (logupMidRelation F n M params).language
      (logupAfterSumcheckRelation F n M params).language
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0).language
      (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
        (Fin.last n)).language
      (Verifier.compatStatement (logupSumcheckContextLens F n M params).stmt
        (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.toVerifier) where
  proj_sound := by
    rintro ⟨stmt, oStmt⟩ hOuter hInner
    simp only [Set.mem_language_iff] at hInner
    rcases hInner with ⟨w, hInner⟩
    cases w
    apply hOuter
    simp only [Set.mem_language_iff]
    refine ⟨(), ?_⟩
    unfold logupMidRelation
    simp only [Set.mem_setOf_eq]
    exact (logupSumcheckRelationInput_iff (F := F) (n := n) (M := M)
      (params := params)).mp hInner
  lift_sound := by
    intro outerStmt innerStmtOut hCompat hInner hOuter
    simp only [Set.mem_language_iff] at hInner hOuter
    rcases hOuter with ⟨w, hOuter⟩
    cases w
    have hOStmt :
        innerStmtOut.2 = logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2 := by
      exact sumcheckVerifier_compat_oracleStmt (oSpec := oSpec) (F := F) (n := n) (M := M)
        (params := params) hCompat
    apply hInner
    refine ⟨(), ?_⟩
    have hPair :
        (innerStmtOut.1, logupSumcheckOracleStmt F n M params outerStmt.1 outerStmt.2) =
          innerStmtOut := by
      cases innerStmtOut
      simpa using hOStmt.symm
    simpa [hPair, logupSumcheckContextLens, logupAfterSumcheckRelation] using hOuter

private theorem OracleVerifier.soundness_mono
    {V : OracleVerifier oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params)
      (StmtAfterSumcheck F n M params) (OStmtAfterOuter F n M params)
      (Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n)}
    {langIn : Set (StmtAfterOuter F n M params × ∀ i, OStmtAfterOuter F n M params i)}
    {langOut : Set (StmtAfterSumcheck F n M params × ∀ i, OStmtAfterOuter F n M params i)}
    {e₁ e₂ : ℝ≥0}
    (h : V.soundness init impl langIn langOut e₁) (hle : e₁ ≤ e₂) :
    V.soundness init impl langIn langOut e₂ := by
  unfold OracleVerifier.soundness Verifier.soundness at h ⊢
  intro WitIn WitOut witIn prover stmtIn hstmt
  exact le_trans (h WitIn WitOut witIn prover stmtIn hstmt) (by exact_mod_cast hle)

set_option linter.unusedDecidableInType false in
/-- Soundness of the outer LogUp phase, with the conservative error `logupOuterSoundnessError`.

The hypothesis `hcard : |H| < |F|` is retained from the paper-shaped statement; the current formal
bound itself is an unconditional union bound over occurrence poles, cleared-identity roots, bad
`z`, and bad batching scalars. -/
theorem logup_outer_soundness
    (hcard : Fintype.card (Fin n → Fin 2) < Fintype.card F) :
    (outerVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language (logupMidRelation F n M params).language
      (logupOuterSoundnessError F n M params) := by
  exact logup_outer_soundness_from_local_algebra
    (oSpec := oSpec) (F := F) (n := n) (M := M) (params := params)
    (init := init) (impl := impl) hcard
    (fun stmt oStmt multiplicity hnot =>
      clearedLookupIdentity_ne_zero_of_not_input (F := F) (n := n) (M := M)
        stmt oStmt multiplicity hnot)
    (fun table columns multiplicity =>
      clearedLookupIdentity_natDegree_le (F := F) (n := n) (M := M)
        table columns multiplicity)
    (fun table columns multiplicity hpoly =>
      clearedLookupIdentity_bad_x_card_le (F := F) (n := n) (M := M)
        table columns multiplicity hpoly)
    (fun K c₀ c hNonzero => random_linear_batch_zero_prob_le (F := F) K c₀ c hNonzero)

set_option linter.unusedFintypeInType false in
/-- Soundness of the embedded sumcheck phase, with error `sumcheckSoundnessError`.

This is the soundness of ArkLib's generic sumcheck reduction lifted through the LogUp context lens;
the bound `sumcheckSoundnessError` is supplied by the generic sumcheck soundness result. -/
theorem logup_sumcheck_soundness (sumcheckSoundnessError : ℝ≥0)
    (hSumcheckSoundness :
      logupSumcheckSoundnessError F n M params ≤ sumcheckSoundnessError) :
    (sumcheckVerifier oSpec F n M params).soundness init impl
      (logupMidRelation F n M params).language
      (logupAfterSumcheckRelation F n M params).language
      sumcheckSoundnessError := by
  classical
  letI : Inhabited F := ⟨0⟩
  letI : Inhabited (Sumcheck.Spec.StatementRound F n (Fin.last n)) :=
    ⟨{ target := 0, challenges := fun _ => 0 }⟩
  let rbrErr :
      (Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n).ChallengeIdx → ℝ≥0 :=
    fun _ => ((logupSumcheckDegree M params : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
  have hKS :
      (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.rbrKnowledgeSoundness
        init impl
        (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F) 0)
        (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
          (Fin.last n))
        rbrErr := by
    simpa [logupConcreteSumcheckOracleReduction, rbrErr] using
      (Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness
        (R := F) (deg := logupSumcheckDegree M params) (D := booleanDomain F)
        (n := n) (oSpec := oSpec) (init := init) (impl := impl))
  have hRbrInner :
      (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier.rbrSoundness
        init impl
        (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
          0).language
        (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (booleanDomain F)
          (Fin.last n)).language
        rbrErr := by
    unfold OracleVerifier.rbrKnowledgeSoundness at hKS
    unfold OracleVerifier.rbrSoundness
    exact Verifier.rbrKnowledgeSoundness_implies_rbrSoundness
      (init := init) (impl := impl) (h := hKS)
  have hRbrLift :
      (sumcheckVerifier oSpec F n M params).rbrSoundness init impl
        (logupMidRelation F n M params).language
        (logupAfterSumcheckRelation F n M params).language
        rbrErr := by
    simpa [sumcheckVerifier] using
      (OracleVerifier.liftContext_rbr_soundness
        (init := init) (impl := impl)
        (V := (logupConcreteSumcheckOracleReduction oSpec F n M params).verifier)
        (lens := (logupSumcheckContextLens F n M params).stmt)
        hRbrInner)
  have hSoundConcrete :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        (logupMidRelation F n M params).language
        (logupAfterSumcheckRelation F n M params).language
        (logupSumcheckSoundnessError F n M params) := by
    unfold OracleVerifier.rbrSoundness at hRbrLift
    unfold OracleVerifier.soundness
    have hSound :=
      Verifier.rbrSoundness_implies_soundness
        (init := init) (impl := impl)
        ((logupMidRelation F n M params).language)
        ((logupAfterSumcheckRelation F n M params).language)
        ((sumcheckVerifier oSpec F n M params).toVerifier)
        rbrErr hRbrLift
    convert hSound using 1
  exact OracleVerifier.soundness_mono (oSpec := oSpec) (F := F) (n := n) (M := M)
    (params := params) (init := init) (impl := impl) hSoundConcrete hSumcheckSoundness

omit [SampleableType F] in
/-- Soundness of the final LogUp point check, with error `logupFinalCheckSoundnessError`
(paper's `ε₂ = K/|F|`). -/
theorem logup_finalCheck_soundness :
    (finalCheckVerifier oSpec F n M params).soundness init impl
      (logupAfterSumcheckRelation F n M params).language
      outputRelation.language
      (logupFinalCheckSoundnessError F M params) := by
  classical
  unfold OracleVerifier.soundness Verifier.soundness
  intro WitIn WitOut witIn prover stmtPair hstmt
  obtain ⟨stmt, oStmt⟩ := stmtPair
  -- The final point check is deterministic (`finalCheckPSpec = ProtocolSpec 0`): the verifier just
  -- queries the retained oracles at `r` and runs one guard. For inputs outside the language that
  -- guard fails, so the verifier rejects and the soundness probability is `0`.
  -- Step 1: the guard `qAtPoint(…) = target` fails on `(stmt, oStmt) ∉ language`.
  have hNe : MvPolynomial.eval stmt.finalClaim.challenges
        (logupQPolynomial (params.group) (oStmt (.input .table)).1
          (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
          (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.outer.batchingScalars) ≠ stmt.finalClaim.target := by
    rw [Set.mem_language_iff, not_exists] at hstmt
    intro he
    refine hstmt () ?_
    show ((stmt, oStmt), ()) ∈ logupAfterSumcheckRelation F n M params
    unfold logupAfterSumcheckRelation Sumcheck.Spec.relationRound
    simp only [Set.mem_setOf_eq, logupSumcheckOracleStmt, logupSumcheckPolynomial]
    have tailSize_zero : n - (Fin.last n : Fin (n + 1)) = 0 := by simp
    let tail0 : Fin (n - (Fin.last n : Fin (n + 1))) → F :=
      fun i => Fin.elim0 (Fin.cast (by simp) i)
    have hfinalPoint :
        Fin.append stmt.finalClaim.challenges tail0 ∘
            Fin.cast (Sumcheck.Spec.relationRound._proof_1 n (Fin.last n)) =
          stmt.finalClaim.challenges := by
      funext i
      change Fin.append stmt.finalClaim.challenges tail0
          (Fin.cast (Sumcheck.Spec.relationRound._proof_1 n (Fin.last n)) i) =
        stmt.finalClaim.challenges i
      rw [Fin.append_right_nil stmt.finalClaim.challenges tail0 tailSize_zero]
      congr 1
    have hsum :
        (∑ x ∈ Fintype.piFinset fun _ : Fin (n - (Fin.last n : Fin (n + 1))) =>
            Finset.univ.map (booleanDomain F),
          MvPolynomial.eval
            (Fin.append stmt.finalClaim.challenges x ∘
              Fin.cast (Sumcheck.Spec.relationRound._proof_1 n (Fin.last n)))
            (logupQPolynomial (params.group) (oStmt (.input .table)).1
              (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
              (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
              stmt.outer.batchingScalars)) =
          MvPolynomial.eval stmt.finalClaim.challenges
            (logupQPolynomial (params.group) (oStmt (.input .table)).1
              (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
              (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
              stmt.outer.batchingScalars) := by
      rw [Finset.sum_eq_single tail0]
      · rw [hfinalPoint]
        rfl
      · intro b _ hb
        exact False.elim (hb (funext fun i => Fin.elim0 (Fin.cast (by simp) i)))
      · intro hnot
        exact False.elim (hnot (by
          rw [Fintype.mem_piFinset]
          intro i
          exact Fin.elim0 (Fin.cast tailSize_zero i)))
    rw [hsum]
    exact he
  -- Step 2: rephrase the guard failure in terms of the oracle answers the verifier reads.
  have hGuardFail : qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
        stmt.finalClaim.challenges stmt.outer.batchingScalars
        (MvPolynomial.eval stmt.finalClaim.challenges (oStmt .multiplicity).1)
        (MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input .table)).1)
        (fun i => MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input (.column i))).1)
        (fun k => MvPolynomial.eval stmt.finalClaim.challenges (oStmt .helpers k).1) ≠
      stmt.finalClaim.target := by
    intro hEq
    exact hNe ((logupQPolynomial_eval_point (params.group) (oStmt (.input .table)).1
      (fun i => (oStmt (.input (.column i))).1) (oStmt .multiplicity).1
      (fun k => (oStmt .helpers k).1) stmt.outer.xChallenge stmt.outer.zChallenge
      stmt.finalClaim.challenges stmt.outer.batchingScalars).trans hEq)
  -- Step 3: the verifier rejects (`finalCheckPSpec` has no messages, and `verify` ignores its
  -- empty challenges), so `simulateQ` of the verification computation is `pure none`.
  let qImpl :
      QueryImpl
        (oSpec + ([OStmtAfterOuter F n M params]ₒ + [finalCheckPSpec.Message]ₒ))
        (OracleComp oSpec) :=
    OracleInterface.simOracle2.{0, 0, 0} (T₁ := OStmtAfterOuter F n M params)
      (T₂ := finalCheckPSpec.Message) oSpec oStmt
      (fun i : finalCheckPSpec.MessageIdx => Fin.elim0 i)
  have hquery :
      ∀ (i : OuterOracleIdx M)
        (q : (instOStmtAfterOuterOracleInterface (F := F) (n := n) (params := params) i).Query),
        simulateQ qImpl ((finalCheckQuery oSpec F n M params i q).run) =
          (pure (some ((instOStmtAfterOuterOracleInterface
            (F := F) (n := n) (params := params) i).answer (oStmt i) q)) :
            OracleComp oSpec _) := by
    intro i q
    simp only [finalCheckQuery, OptionT.run_mk, simulateQ_map, qImpl,
      OracleInterface.simOracle2, QueryImpl.addLift_def, simulateQ_query,
      QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply, QueryImpl.add,
      OracleInterface.simOracle0, OracleInterface.answer, OracleQuery.cont_query,
      OracleQuery.input_query]
    change some <$> id <$>
        (pure (ReaderT.run (OracleInterface.toOC.impl q) (oStmt i)) :
          OracleComp oSpec _) =
      (pure (some (ReaderT.run (OracleInterface.toOC.impl q) (oStmt i))) :
        OracleComp oSpec _)
    simp
  let colValue := fun i : Fin M =>
    MvPolynomial.eval stmt.finalClaim.challenges (oStmt (.input (.column i))).1
  let helperValue := fun k : Fin params.numGroups =>
    MvPolynomial.eval stmt.finalClaim.challenges (oStmt .helpers k).1
  have hGuardFail' :
      qAtPoint (params.group) stmt.outer.xChallenge stmt.outer.zChallenge
          stmt.finalClaim.challenges stmt.outer.batchingScalars
          (OracleInterface.answer (oStmt .multiplicity) stmt.finalClaim.challenges)
          (OracleInterface.answer (oStmt (.input .table)) stmt.finalClaim.challenges)
          colValue helperValue ≠
        stmt.finalClaim.target := by
    simpa [OracleInterface.answer, colValue, helperValue] using hGuardFail
  have hVerifyNone :
      simulateQ qImpl
          ((finalCheckVerifier oSpec F n M params).verify stmt (fun i => Fin.elim0 i)).run =
        (pure none : OracleComp oSpec (Option StmtOut)) := by
    simp only [finalCheckVerifier, OptionT.run_bind, OptionT.run_pure]
    erw [simulateQ_bind]
    rw [hquery .multiplicity stmt.finalClaim.challenges]
    simp only [pure_bind, Option.elim_some]
    erw [simulateQ_bind]
    rw [hquery (.input .table) stmt.finalClaim.challenges]
    simp only [pure_bind, Option.elim_some]
    have hcols := simulateQ_optionT_mapM_pure qImpl
      (fun i : Fin M =>
        finalCheckQuery oSpec F n M params (.input (.column i)) stmt.finalClaim.challenges)
      colValue (Vector.finRange M) (by
        intro i
        simpa [colValue, OracleInterface.answer] using
          hquery (.input (.column i)) stmt.finalClaim.challenges)
    erw [simulateQ_option_elimM]
    erw [hcols]
    simp only [pure_bind, Option.elimM, Option.elim_some]
    have hhelpers := simulateQ_optionT_mapM_pure qImpl
      (fun k : Fin params.numGroups =>
        finalCheckQuery oSpec F n M params .helpers ⟨k, stmt.finalClaim.challenges⟩)
      helperValue (Vector.finRange params.numGroups) (by
        intro k
        simpa [helperValue, OracleInterface.answer] using
          hquery .helpers ⟨k, stmt.finalClaim.challenges⟩)
    erw [simulateQ_option_elimM]
    erw [hhelpers]
    simp only [pure_bind, Option.elimM, Option.elim_some]
    erw [simulateQ_option_elimM]
    simp [guard, hGuardFail', Option.elimM]
  -- Step 4: the verifier rejects for every transcript (the empty one), so the `toVerifier`
  -- verification computation is `pure none`.
  have hRejectRun :
      ∀ t : finalCheckPSpec.FullTranscript,
        OptionT.run
            ((finalCheckVerifier oSpec F n M params).toVerifier.verify ⟨stmt, oStmt⟩ t) =
          (pure none : OracleComp oSpec (Option (StmtOut × (∀ i, OStmtOut i)))) := by
    intro t
    obtain rfl : t = default := Unique.eq_default t
    simp only [OracleVerifier.toVerifier, OptionT.run_bind]
    have hInner :
        simulateQ
            (OracleInterface.simOracle2 oSpec oStmt
              (ProtocolSpec.FullTranscript.messages
                (default : finalCheckPSpec.FullTranscript)))
            (((finalCheckVerifier oSpec F n M params).verify stmt
              (ProtocolSpec.FullTranscript.challenges
                (default : finalCheckPSpec.FullTranscript))).run) =
          (pure none : OracleComp oSpec (Option StmtOut)) := by
      simpa [qImpl, finalCheckPSpec] using hVerifyNone
    have hInnerT :
        OptionT.run
          (simulateQ
            (OracleInterface.simOracle2 oSpec oStmt
              (ProtocolSpec.FullTranscript.messages default))
            ((finalCheckVerifier oSpec F n M params).verify stmt
              (ProtocolSpec.FullTranscript.challenges default))) =
          (pure none : OracleComp oSpec (Option StmtOut)) := by
      simpa [OptionT.run, finalCheckPSpec] using hInner
    erw [hInnerT]
    simp
  -- Step 5: with the verifier rejecting, the whole reduction never produces output, so its run
  -- is always `none` and the soundness event has probability `0 ≤ bound`.
  refine le_trans (le_of_eq ?_) (zero_le)
  refine probEvent_eq_zero (fun x hx => ?_)
  exfalso
  rw [OptionT.mem_support_iff, OptionT.run_mk] at hx
  simp only [support_bind, Set.mem_iUnion] at hx
  obtain ⟨s, -, hx⟩ := hx
  have hrunNone :
      OptionT.run
          ((Reduction.mk prover (finalCheckVerifier oSpec F n M params).toVerifier).run
            ⟨stmt, oStmt⟩ witIn) =
        ((fun _ => none) <$> prover.run ⟨stmt, oStmt⟩ witIn) := by
    simp only [Reduction.run, Verifier.run, map_eq_bind_pure_comp, OptionT.run_bind,
      OptionT.run_monadLift, monadLift_self, Option.getM, Option.elimM, bind_assoc]
    refine bind_congr fun pr => ?_
    simp only [Function.comp_apply, pure_bind, Option.elim_some]
    rw [hRejectRun pr.1]
    simp
  rw [hrunNone, simulateQ_map] at hx
  simp only [StateT.run'_map', support_map, Set.mem_image] at hx
  obtain ⟨_, _, hx⟩ := hx
  cases hx

/-- Main ArkLib soundness theorem for the LogUp protocol.

Obtained by composing the three per-phase soundness lemmas with `OracleVerifier.append_soundness`,
following the protocol's `outer ++ sumcheck ++ finalCheck` structure: the total error is the sum
of the three per-phase errors. -/
theorem logup_soundness (sumcheckSoundnessError : ℝ≥0)
    (hSumcheckSoundness :
      logupSumcheckSoundnessError F n M params ≤ sumcheckSoundnessError)
    (hcard : Fintype.card (Fin n → Fin 2) < Fintype.card F) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) := by
  unfold logupVerifier logupSoundnessError
  refine OracleVerifier.append_soundness.{0, 0, 0, 0}
    (lang₂ := (logupAfterSumcheckRelation F n M params).language) _ _
    (OracleVerifier.append_soundness
      (lang₂ := (logupMidRelation F n M params).language) _ _ ?_ ?_) ?_
  · exact logup_outer_soundness oSpec F n M params init impl hcard
  · exact logup_sumcheck_soundness oSpec F n M params init impl sumcheckSoundnessError
      hSumcheckSoundness
  · exact logup_finalCheck_soundness oSpec F n M params init impl

end Soundness

end Logup

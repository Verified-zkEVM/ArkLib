import ArkLib.Data.MvPolynomial.Multilinear
import Mathlib.Algebra.Order.Floor.Div

/-!
# LogUp algebra and sumcheck polynomial

This file contains the protocol-independent algebra used to express LogUp as a sumcheck claim. It
does not define statements, transcripts, provers, or verifiers. Instead, it works with plain
hypercube functions `(Fin n → Fin 2) → F`, polynomial inputs `MvPolynomial (Fin n) F`, challenges,
and partial-sum groups.

The main output is `logupQPolynomial`, the polynomial `Q` that the protocol sends to sumcheck, plus
`logupQPolynomial_degreeOf`, the individual-degree bound needed by sumcheck. The row-level and
point-level definitions in this file are the semantic versions used to connect `Q` back to honest
LogUp data and to the verifier's final point check.

## Sections

* **Generic batched polynomial** defines the abstract polynomial shape used by the sumcheck claim:
  for each helper group, multiply by the relevant denominators to clear fractions, then batch all
  group identities with the equality-polynomial weight and verifier scalars. This section also
  proves the generic individual-degree bound, so the later LogUp-specific proof only has to show
  that its ingredients are multilinear.
* **Term indexing** gives names to the `M + 1` fractional terms. The table term has input label
  `InputIdx.table` and paper index `0`; lookup column `j` has input label `InputIdx.column j` and
  paper index `j + 1`. The conversion lemmas here keep later sums over `Fin (M + 1)` aligned with
  the table/column oracle labels.
* **Fractional-identity algebra** defines the row-wise LogUp quantities on the Boolean hypercube.
  It computes the normalized table multiplicity, forms the logarithmic-derivative terms
  `mᵢ(u) / φᵢ(u)` for the table and lookup columns, groups those terms into helper values, clears
  denominators inside each group, and combines the cleared identities into the row value
  `qOnHypercube`.
* **Final-point reconstructions** defines the verifier-side version of the same expressions at
  sumcheck's final point `r`. At this point the verifier has scalar oracle answers `m(r)`, `t(r)`,
  `fᵢ(r)`, and `hₖ(r)`, not whole row functions, so this section rebuilds the value that should
  equal the final sumcheck claim.
* **The LogUp polynomial** builds the actual multivariate polynomial `Q` from the table, column,
  multiplicity, and helper polynomials. It instantiates the generic batched polynomial with LogUp's
  concrete denominator and numerator polynomials, then proves the `M + 3` individual-degree bound
  required by ArkLib's generic sumcheck protocol.
-/

namespace Logup

open scoped BigOperators

/-! ## Generic batched polynomial -/

section BatchedPolynomial

variable {F : Type} [Field F] {n T K : ℕ}
variable (groups : Fin K → Finset (Fin T))
variable (phiPoly numerPoly : Fin T → MvPolynomial (Fin n) F)
variable (helperPoly : Fin K → MvPolynomial (Fin n) F)

/-- One group's cleared-denominator identity, as a polynomial in abstract per-term denominator
(`phiPoly`) and numerator (`numerPoly`) polynomials and per-group helper polynomials. -/
noncomputable def batchedDomainIdentity (k : Fin K) : MvPolynomial (Fin n) F :=
  helperPoly k * (∏ i ∈ groups k, phiPoly i) -
    ∑ i ∈ groups k, numerPoly i * ∏ j ∈ (groups k).erase i, phiPoly j

/-- The generic batched sumcheck polynomial: a `λ`-batched sum of per-group cleared-denominator
identities, weighted by an equality kernel. Independent of any particular protocol. -/
noncomputable def batchedSumcheckPolynomial
    (zChallenge : Fin n → F) (batchingScalars : Fin K → F) : MvPolynomial (Fin n) F :=
  ∑ k : Fin K, (helperPoly k +
    MvPolynomial.eqPolynomial zChallenge * MvPolynomial.C (batchingScalars k) *
      batchedDomainIdentity groups phiPoly numerPoly helperPoly k)

private theorem prod_phiPoly_degreeOf
    (hphi : ∀ i v, MvPolynomial.degreeOf v (phiPoly i) ≤ 1)
    (s : Finset (Fin T)) (v : Fin n) :
    MvPolynomial.degreeOf v (∏ i ∈ s, phiPoly i) ≤ T := by
  calc
    _ ≤ ∑ i ∈ s, MvPolynomial.degreeOf v (phiPoly i) := MvPolynomial.degreeOf_prod_le v _ _
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum (fun i _ => hphi i v)
    _ = s.card := by simp
    _ ≤ T := le_trans (Finset.card_le_univ s) (by simp)

/-- Each group identity has individual degree at most `T + 1`. -/
theorem batchedDomainIdentity_degreeOf
    (hphi : ∀ i v, MvPolynomial.degreeOf v (phiPoly i) ≤ 1)
    (hnumer : ∀ i v, MvPolynomial.degreeOf v (numerPoly i) ≤ 1)
    (hhelper : ∀ k v, MvPolynomial.degreeOf v (helperPoly k) ≤ 1)
    (k : Fin K) (v : Fin n) :
    MvPolynomial.degreeOf v (batchedDomainIdentity groups phiPoly numerPoly helperPoly k)
      ≤ T + 1 := by
  unfold batchedDomainIdentity
  have hLeft :
      MvPolynomial.degreeOf v (helperPoly k * (∏ i ∈ groups k, phiPoly i)) ≤ T + 1 := by
    calc
      _ ≤ MvPolynomial.degreeOf v (helperPoly k) +
          MvPolynomial.degreeOf v (∏ i ∈ groups k, phiPoly i) := MvPolynomial.degreeOf_mul_le v _ _
      _ ≤ 1 + T := by
        gcongr
        · exact hhelper k v
        · exact prod_phiPoly_degreeOf phiPoly hphi (groups k) v
      _ = T + 1 := by omega
  have hRight :
      MvPolynomial.degreeOf v
        (∑ i ∈ groups k, numerPoly i * ∏ j ∈ (groups k).erase i, phiPoly j) ≤ T + 1 := by
    calc
      _ ≤ (groups k).sup fun i =>
          MvPolynomial.degreeOf v (numerPoly i * ∏ j ∈ (groups k).erase i, phiPoly j) :=
        MvPolynomial.degreeOf_sum_le v _ _
      _ ≤ T + 1 := by
        apply Finset.sup_le
        intro i _
        calc
          _ ≤ MvPolynomial.degreeOf v (numerPoly i) +
              MvPolynomial.degreeOf v (∏ j ∈ (groups k).erase i, phiPoly j) :=
            MvPolynomial.degreeOf_mul_le v _ _
          _ ≤ 1 + T := by
            gcongr
            · exact hnumer i v
            · exact prod_phiPoly_degreeOf phiPoly hphi ((groups k).erase i) v
          _ = T + 1 := by omega
  exact (MvPolynomial.degreeOf_sub_le v _ _).trans (max_le hLeft hRight)

/-- The batched polynomial has individual degree at most `T + 2`. -/
theorem batchedSumcheckPolynomial_degreeOf
    (zChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (hphi : ∀ i v, MvPolynomial.degreeOf v (phiPoly i) ≤ 1)
    (hnumer : ∀ i v, MvPolynomial.degreeOf v (numerPoly i) ≤ 1)
    (hhelper : ∀ k v, MvPolynomial.degreeOf v (helperPoly k) ≤ 1)
    (v : Fin n) :
    MvPolynomial.degreeOf v
        (batchedSumcheckPolynomial groups phiPoly numerPoly helperPoly zChallenge batchingScalars)
      ≤ T + 2 := by
  unfold batchedSumcheckPolynomial
  calc
    _ ≤ (Finset.univ : Finset (Fin K)).sup fun k =>
        MvPolynomial.degreeOf v
          (helperPoly k +
            MvPolynomial.eqPolynomial zChallenge * MvPolynomial.C (batchingScalars k) *
              batchedDomainIdentity groups phiPoly numerPoly helperPoly k) :=
      MvPolynomial.degreeOf_sum_le v _ _
    _ ≤ T + 2 := by
      apply Finset.sup_le
      intro k _
      have hHelper :
          MvPolynomial.degreeOf v (helperPoly k) ≤ T + 2 := (hhelper k v).trans (by omega)
      have hProduct :
          MvPolynomial.degreeOf v
            (MvPolynomial.eqPolynomial zChallenge * MvPolynomial.C (batchingScalars k) *
              batchedDomainIdentity groups phiPoly numerPoly helperPoly k) ≤ T + 2 := by
        calc
          _ ≤ MvPolynomial.degreeOf v
                (MvPolynomial.eqPolynomial zChallenge * MvPolynomial.C (batchingScalars k)) +
              MvPolynomial.degreeOf v
                (batchedDomainIdentity groups phiPoly numerPoly helperPoly k) :=
            MvPolynomial.degreeOf_mul_le v _ _
          _ ≤ (MvPolynomial.degreeOf v (MvPolynomial.eqPolynomial zChallenge) +
                MvPolynomial.degreeOf v (MvPolynomial.C (batchingScalars k))) +
              MvPolynomial.degreeOf v
                (batchedDomainIdentity groups phiPoly numerPoly helperPoly k) := by
            gcongr
            exact MvPolynomial.degreeOf_mul_le v _ _
          _ ≤ (1 + 0) + (T + 1) := by
            gcongr
            · exact MvPolynomial.eqPolynomial_degreeOf (R := F) zChallenge v
            · exact (MvPolynomial.degreeOf_C (R := F) (batchingScalars k) v).le
            · exact batchedDomainIdentity_degreeOf groups phiPoly numerPoly helperPoly
                hphi hnumer hhelper k v
          _ = T + 2 := by omega
      exact (MvPolynomial.degreeOf_add_le v _ _).trans (max_le hHelper hProduct)

end BatchedPolynomial

/-! ## Term indexing

LogUp has `M + 1` terms: term `0` is the table, terms `1, …, M` are the lookup columns. -/

/-- Labels for the `M + 1` LogUp terms: the table and the `M` lookup columns. -/
inductive InputIdx (M : ℕ) where
  | table : InputIdx M
  | column : Fin M → InputIdx M
deriving DecidableEq

/-- Term labels `0, ..., M` from the paper, with `0` denoting the table term. -/
@[reducible]
def TermIdx (M : ℕ) : Type :=
  Fin (M + 1)

/-- Interpret term index `0` as the table and term indices `1, ..., M` as lookup columns. -/
def termToInput {M : ℕ} (i : TermIdx M) : InputIdx M :=
  if h : i.val = 0 then .table else .column ⟨i.val - 1, by omega⟩

/-- Interpret a table/column label as its term index `0, ..., M`. -/
def inputToTerm {M : ℕ} : InputIdx M → TermIdx M
  | .table => ⟨0, by omega⟩
  | .column i => ⟨i.val + 1, by omega⟩

@[simp]
theorem termToInput_inputToTerm {M : ℕ} (i : InputIdx M) :
    termToInput (inputToTerm i) = i := by
  cases i <;> simp [termToInput, inputToTerm]

@[simp]
theorem inputToTerm_termToInput {M : ℕ} (i : TermIdx M) :
    inputToTerm (termToInput i) = i := by
  unfold termToInput
  split
  · next h => exact Fin.ext h.symm
  · next h => apply Fin.ext; simp only [inputToTerm]; omega

/-! ## Fractional-identity algebra

LogUp's logarithmic-derivative construction, evaluated on hypercube rows. The table, columns,
multiplicity, and helper functions are bare hypercube functions `(Fin n → Fin 2) → F`. -/

section Algebra

variable {F : Type} [Field F] {n M K : ℕ}

/-- Number of table rows with value `a`. -/
def tableMultiplicityCount [Fintype F] [DecidableEq F] (table : (Fin n → Fin 2) → F) (a : F) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 2)).filter fun u => table u = a).card

/-- Total number of lookup-column entries with value `a`. -/
def lookupMultiplicityCount [Fintype F] [DecidableEq F]
    (columns : Fin M → (Fin n → Fin 2) → F) (a : F) : ℕ :=
  ((Finset.univ : Finset (Fin M × (Fin n → Fin 2))).filter fun ix => columns ix.1 ix.2 = a).card

/-- The normalized multiplicity from paper equation (14), evaluated at one table row. -/
noncomputable def normalizedMultiplicityValue [Fintype F] [DecidableEq F]
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F) (u : Fin n → Fin 2) : F :=
  let a := table u
  (lookupMultiplicityCount columns a : F) / (tableMultiplicityCount table a : F)

/-- The denominator term `φᵢ(u)` from Protocol 2. -/
noncomputable def phi (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (xChallenge : F) : InputIdx M → (Fin n → Fin 2) → F
  | .table => fun u => xChallenge + table u
  | .column i => fun u => xChallenge + columns i u

/-- The numerator term `mᵢ(u)`, with `m₀ = m` and `mᵢ = -1` for columns. -/
noncomputable def numerator (multiplicity : (Fin n → Fin 2) → F) :
    InputIdx M → (Fin n → Fin 2) → F
  | .table => multiplicity
  | .column _ => fun _ => -1

/-- The denominator term, indexed as `0, ..., M` as in the paper. -/
noncomputable def termPhi (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (xChallenge : F) (i : TermIdx M) (u : Fin n → Fin 2) : F :=
  phi table columns xChallenge (termToInput i) u

/-- The numerator term, indexed as `0, ..., M` as in the paper. -/
noncomputable def termNumerator (multiplicity : (Fin n → Fin 2) → F)
    (i : TermIdx M) (u : Fin n → Fin 2) : F :=
  numerator multiplicity (termToInput i) u

/-- The domain-identity expression for one helper function `hₖ`. -/
noncomputable def domainIdentityTerm (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (k : Fin K) (u : Fin n → Fin 2) : F :=
  helpers k u * (∏ i ∈ groups k, termPhi table columns xChallenge i u) -
    ∑ i ∈ groups k,
      termNumerator multiplicity i u * ∏ j ∈ (groups k).erase i, termPhi table columns xChallenge j u

/-- The helper value `hₖ(u) = Σᵢ mᵢ(u)/φᵢ(u)` from paper equation (16). -/
noncomputable def helperValue (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (xChallenge : F) (k : Fin K) (u : Fin n → Fin 2) : F :=
  ∑ i ∈ groups k, termNumerator multiplicity i u / termPhi table columns xChallenge i u

/-- The batched polynomial expression `Q` from paper equation (18), evaluated on a row `u ∈ H`. -/
noncomputable def qOnHypercube (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (zChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (u : Fin n → Fin 2) : F :=
  ∑ k : Fin K, (
    helpers k u +
      MvPolynomial.eval (u : Fin n → F) (MvPolynomial.eqPolynomial zChallenge) *
        batchingScalars k *
        domainIdentityTerm groups table columns multiplicity helpers xChallenge k u)

/-- Honest helper values make the cleared-denominator identity vanish pointwise, away from poles. -/
theorem domainIdentityTerm_eq_zero (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (k : Fin K) (u : Fin n → Fin 2)
    (hh : helpers k u = helperValue groups table columns multiplicity xChallenge k u)
    (hφ : ∀ i ∈ groups k, termPhi table columns xChallenge i u ≠ 0) :
    domainIdentityTerm groups table columns multiplicity helpers xChallenge k u = 0 := by
  rw [domainIdentityTerm, hh, helperValue, Finset.sum_mul, sub_eq_zero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← Finset.mul_prod_erase _ _ hi]
  field_simp [hφ i hi]

/-- The normalized multiplicity makes the table-side logarithmic derivative equal the sum of the
lookup-column logarithmic derivatives. -/
theorem honest_multiplicity_identity [Fintype F] [DecidableEq F]
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F) (xChallenge : F)
    (hcols : ∀ j : Fin M, ∀ u : Fin n → Fin 2, ∃ v : Fin n → Fin 2,
      columns j u = table v)
    (hchar : ∀ a : F, lookupMultiplicityCount columns a ≠ 0 →
      (tableMultiplicityCount table a : F) ≠ 0) :
    (∑ u : Fin n → Fin 2,
        normalizedMultiplicityValue table columns u / (xChallenge + table u))
      = ∑ j : Fin M, ∑ u : Fin n → Fin 2,
          (1 : F) / (xChallenge + columns j u) := by
  classical
  have key : ∀ a : F,
      tableMultiplicityCount table a •
          ((lookupMultiplicityCount columns a : F) /
            (tableMultiplicityCount table a : F) / (xChallenge + a))
        = lookupMultiplicityCount columns a • ((1 : F) / (xChallenge + a)) := by
    intro a
    by_cases hT : tableMultiplicityCount table a = 0
    · have hL : lookupMultiplicityCount columns a = 0 := by
        rw [lookupMultiplicityCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨j, u⟩ - hja
        obtain ⟨v, hv⟩ := hcols j u
        have hav : table v = a := hv.symm.trans hja
        rw [tableMultiplicityCount] at hT
        exact absurd hT (Finset.card_ne_zero_of_mem
          (show v ∈ Finset.univ.filter (fun w => table w = a) by simp [hav]))
      simp [hT, hL]
    · rw [nsmul_eq_mul, nsmul_eq_mul]
      by_cases hL : lookupMultiplicityCount columns a = 0
      · simp [hL]
      · have hTF := hchar a hL
        field_simp
  have hLHS :
      (∑ u : Fin n → Fin 2, normalizedMultiplicityValue table columns u /
          (xChallenge + table u))
        = ∑ a : F, tableMultiplicityCount table a •
            ((lookupMultiplicityCount columns a : F) / (tableMultiplicityCount table a : F)
              / (xChallenge + a)) := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n → Fin 2)) table]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h : ∀ u ∈ Finset.univ.filter (fun u => table u = a),
        normalizedMultiplicityValue table columns u / (xChallenge + table u)
          = (lookupMultiplicityCount columns a : F) / (tableMultiplicityCount table a : F)
              / (xChallenge + a) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      change (lookupMultiplicityCount columns (table u) : F) /
            (tableMultiplicityCount table (table u) : F) /
            (xChallenge + table u)
          = (lookupMultiplicityCount columns a : F) /
            (tableMultiplicityCount table a : F) / (xChallenge + a)
      rw [hu]
    rw [Finset.sum_congr rfl h, Finset.sum_const]
    rfl
  have hRHS :
      (∑ j : Fin M, ∑ u : Fin n → Fin 2, (1 : F) / (xChallenge + columns j u))
        = ∑ a : F, lookupMultiplicityCount columns a • ((1 : F) / (xChallenge + a)) := by
    rw [← Finset.sum_product', Finset.univ_product_univ,
      ← Finset.sum_fiberwise (Finset.univ : Finset (Fin M × (Fin n → Fin 2)))
        (fun p => columns p.1 p.2)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h : ∀ p ∈ Finset.univ.filter
          (fun p : Fin M × (Fin n → Fin 2) => columns p.1 p.2 = a),
        (1 : F) / (xChallenge + columns p.1 p.2) = (1 : F) / (xChallenge + a) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [hp]
    rw [Finset.sum_congr rfl h, Finset.sum_const]
    rfl
  rw [hLHS, hRHS]
  exact Finset.sum_congr rfl (fun a _ => key a)

/-- If a lookup value appears in a column and every lookup value appears in the table, then the
corresponding table multiplicity is nonzero as a field element under the LogUp characteristic
bound. -/
theorem tableMultiplicityCount_cast_ne_zero_of_lookupMultiplicityCount_ne_zero [Fintype F]
    [DecidableEq F] (hcharLarge : M * 2 ^ n < ringChar F)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (hcols : ∀ j : Fin M, ∀ u : Fin n → Fin 2, ∃ v : Fin n → Fin 2,
      columns j u = table v)
    {a : F} (hlookup : lookupMultiplicityCount columns a ≠ 0) :
    (tableMultiplicityCount table a : F) ≠ 0 := by
  classical
  have hlookupCard :
      ((Finset.univ : Finset (Fin M × (Fin n → Fin 2))).filter fun ix =>
        columns ix.1 ix.2 = a).card ≠ 0 := by
    simpa [lookupMultiplicityCount] using hlookup
  obtain ⟨⟨j, u⟩, hju⟩ := Finset.card_ne_zero.mp hlookupCard
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hju
  obtain ⟨v, hv⟩ := hcols j u
  have hvTable : table v = a := hv.symm.trans hju
  have htablePos : 0 < tableMultiplicityCount table a := by
    rw [tableMultiplicityCount, Finset.card_pos]
    exact ⟨v, by simp [hvTable]⟩
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have htable_le_card :
      tableMultiplicityCount table a ≤ Fintype.card (Fin n → Fin 2) := by
    rw [tableMultiplicityCount, ← Finset.card_univ]
    exact Finset.card_filter_le _ _
  have hcard_hypercube : Fintype.card (Fin n → Fin 2) = 2 ^ n := by
    simp
  have hpow_le : 2 ^ n ≤ M * 2 ^ n := by
    have hMone : 1 ≤ M := Nat.succ_le_of_lt hMpos
    nth_rewrite 1 [← Nat.one_mul (2 ^ n)]
    exact Nat.mul_le_mul_right (2 ^ n) hMone
  have htable_lt_char : tableMultiplicityCount table a < ringChar F := by
    calc
      tableMultiplicityCount table a ≤ Fintype.card (Fin n → Fin 2) := htable_le_card
      _ = 2 ^ n := hcard_hypercube
      _ ≤ M * 2 ^ n := hpow_le
      _ < ringChar F := hcharLarge
  intro hzero
  have hdvd : ringChar F ∣ tableMultiplicityCount table a :=
    (ringChar.spec F (tableMultiplicityCount table a)).1 hzero
  exact (Nat.not_dvd_of_pos_of_lt htablePos htable_lt_char) hdvd

/-- If `x` avoids the table poles, then it avoids all table and lookup-column denominator poles
under lookup containment. -/
theorem termPhi_ne_zero_of_table_poles
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F) (xChallenge : F)
    (hcols : ∀ j : Fin M, ∀ u : Fin n → Fin 2, ∃ v : Fin n → Fin 2,
      columns j u = table v)
    (hNoTablePoles : ∀ u : Fin n → Fin 2, xChallenge + table u ≠ 0) :
    ∀ (i : TermIdx M) (u : Fin n → Fin 2), termPhi table columns xChallenge i u ≠ 0 := by
  intro i u
  cases hti : termToInput i with
  | table =>
      rw [termPhi, hti]
      simpa [phi] using hNoTablePoles u
  | column j =>
      obtain ⟨v, hv⟩ := hcols j u
      rw [termPhi, hti, phi]
      simpa [hv] using hNoTablePoles v

/-- The table-pole set has size at most the Boolean hypercube. -/
theorem pole_card_le [Fintype F] [DecidableEq F] (table : (Fin n → Fin 2) → F) :
    (Finset.univ.filter (fun x : F => ∃ u : Fin n → Fin 2, x + table u = 0)).card
      ≤ Fintype.card (Fin n → Fin 2) := by
  classical
  calc
    (Finset.univ.filter (fun x : F => ∃ u : Fin n → Fin 2, x + table u = 0)).card
        ≤ (Finset.univ.image (fun u : Fin n → Fin 2 => -table u)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          obtain ⟨u, hu⟩ := hx
          exact Finset.mem_image.mpr
            ⟨u, Finset.mem_univ u, (eq_neg_of_add_eq_zero_left hu).symm⟩
    _ ≤ Fintype.card (Fin n → Fin 2) := by
        rw [← Finset.card_univ]
        exact Finset.card_image_le

/-- The honest row-wise LogUp claim sums to zero away from denominator poles. -/
theorem logupOuterClaim_zero [Fintype F] [DecidableEq F]
    (groups : Fin K → Finset (TermIdx M))
    (hgroups : ∀ g : TermIdx M → F, (∑ k : Fin K, ∑ i ∈ groups k, g i) = ∑ i : TermIdx M, g i)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (xChallenge : F) (zChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (hcols : ∀ j : Fin M, ∀ u : Fin n → Fin 2, ∃ v : Fin n → Fin 2,
      columns j u = table v)
    (hchar : ∀ a : F, lookupMultiplicityCount columns a ≠ 0 →
      (tableMultiplicityCount table a : F) ≠ 0)
    (hpoles : ∀ (i : TermIdx M) (u : Fin n → Fin 2),
      termPhi table columns xChallenge i u ≠ 0) :
    (∑ u : Fin n → Fin 2,
        qOnHypercube groups table columns (normalizedMultiplicityValue table columns)
          (fun k u => helperValue groups table columns
            (normalizedMultiplicityValue table columns) xChallenge k u)
          xChallenge zChallenge batchingScalars u) = 0 := by
  have hq : ∀ u : Fin n → Fin 2,
      qOnHypercube groups table columns (normalizedMultiplicityValue table columns)
          (fun k u => helperValue groups table columns
            (normalizedMultiplicityValue table columns) xChallenge k u)
          xChallenge zChallenge batchingScalars u
        = ∑ k : Fin K,
            helperValue groups table columns
              (normalizedMultiplicityValue table columns) xChallenge k u := by
    intro u
    simp only [qOnHypercube]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [domainIdentityTerm_eq_zero groups table columns (normalizedMultiplicityValue table columns)
      (fun k u => helperValue groups table columns
        (normalizedMultiplicityValue table columns) xChallenge k u)
      xChallenge k u rfl (fun i _ => hpoles i u), mul_zero, add_zero]
  have hsum : ∀ u : Fin n → Fin 2,
      (∑ k : Fin K,
          helperValue groups table columns
            (normalizedMultiplicityValue table columns) xChallenge k u)
        = ∑ i : TermIdx M,
            termNumerator (normalizedMultiplicityValue table columns) i u /
              termPhi table columns xChallenge i u := by
    intro u
    simp only [helperValue]
    exact hgroups
      (fun i => termNumerator (normalizedMultiplicityValue table columns) i u /
        termPhi table columns xChallenge i u)
  have hterm : ∀ u : Fin n → Fin 2,
      (∑ i : TermIdx M,
          termNumerator (normalizedMultiplicityValue table columns) i u /
            termPhi table columns xChallenge i u)
        = normalizedMultiplicityValue table columns u / (xChallenge + table u)
          + ∑ j : Fin M, (-1 : F) / (xChallenge + columns j u) := by
    intro u
    have hcol : ∀ j : Fin M,
        termNumerator (normalizedMultiplicityValue table columns) (Fin.succ j) u /
            termPhi table columns xChallenge (Fin.succ j) u
          = (-1 : F) / (xChallenge + columns j u) := by
      intro j
      have htt : termToInput (Fin.succ j : TermIdx M) = InputIdx.column j := by
        simp [termToInput]
      simp only [termNumerator, termPhi, htt, numerator, phi]
    rw [Fin.sum_univ_succ]
    refine congrArg₂ (· + ·) rfl ?_
    exact Finset.sum_congr rfl (fun j _ => hcol j)
  simp_rw [hq, hsum, hterm]
  rw [Finset.sum_add_distrib, honest_multiplicity_identity table columns xChallenge hcols hchar,
    Finset.sum_comm (f := fun u j => (-1 : F) / (xChallenge + columns j u)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun u _ => by ring)

end Algebra

/-! ## Final-point reconstructions

The verifier's reconstruction of `Q` at the sumcheck point `r` from the claimed evaluation values
`mVal = m(r)`, `tVal = t(r)`, `colVals i = fᵢ(r)`, `helperVals k = hₖ(r)`. -/

section AtPoint

variable {F : Type} [Field F] {n M K : ℕ}

/-- Denominator term at the final sumcheck point, from the claimed evaluation values. -/
def phiAtPoint (xChallenge tVal : F) (colVals : Fin M → F) : InputIdx M → F
  | .table => xChallenge + tVal
  | .column i => xChallenge + colVals i

/-- Numerator term at the final sumcheck point, from the claimed multiplicity value. -/
def numeratorAtPoint (mVal : F) : InputIdx M → F
  | .table => mVal
  | .column _ => -1

/-- Term denominator at the final sumcheck point, indexed by `0, ..., M`. -/
def termPhiAtPoint (xChallenge tVal : F) (colVals : Fin M → F) (i : TermIdx M) : F :=
  phiAtPoint xChallenge tVal colVals (termToInput i)

/-- Term numerator at the final sumcheck point, indexed by `0, ..., M`. -/
def termNumeratorAtPoint (mVal : F) (i : TermIdx M) : F :=
  numeratorAtPoint mVal (termToInput i)

/-- The domain-identity expression at the final sumcheck point `r`. -/
noncomputable def domainIdentityAtPoint (groups : Fin K → Finset (TermIdx M))
    (xChallenge mVal tVal : F) (colVals : Fin M → F) (helperVals : Fin K → F) (k : Fin K) : F :=
  helperVals k * (∏ i ∈ groups k, termPhiAtPoint xChallenge tVal colVals i) -
    ∑ i ∈ groups k,
      termNumeratorAtPoint mVal i *
        ∏ j ∈ (groups k).erase i, termPhiAtPoint xChallenge tVal colVals j

/-- The verifier's final check value `Q(eq(r,z), m(r), φᵢ(r), hₖ(r))` from paper (19). -/
noncomputable def qAtPoint (groups : Fin K → Finset (TermIdx M))
    (xChallenge : F) (zChallenge rChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (mVal tVal : F) (colVals : Fin M → F) (helperVals : Fin K → F) : F :=
  ∑ k : Fin K, (
    helperVals k +
      MvPolynomial.eval rChallenge (MvPolynomial.eqPolynomial zChallenge) * batchingScalars k *
        domainIdentityAtPoint groups xChallenge mVal tVal colVals helperVals k)

end AtPoint

/-! ## The LogUp polynomial

The input polynomials (table, columns, multiplicity, helpers) combined into LogUp's instantiation of
the generic batched polynomial. -/

section Polynomial

variable {F : Type} [Field F] {n M K : ℕ}

/-- Denominator polynomial `φ` for one term: `x + (its oracle polynomial)`. -/
noncomputable def termPhiPolynomial (table : MvPolynomial (Fin n) F)
    (columns : Fin M → MvPolynomial (Fin n) F) (xChallenge : F) (i : TermIdx M) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C xChallenge +
    match termToInput i with
    | .table => table
    | .column j => columns j

/-- Numerator polynomial for one term: the multiplicity polynomial for the table term, `-1` else. -/
noncomputable def termNumeratorPolynomial (multiplicity : MvPolynomial (Fin n) F) (i : TermIdx M) :
    MvPolynomial (Fin n) F :=
  match termToInput i with
  | .table => multiplicity
  | .column _ => MvPolynomial.C (-1)

theorem termPhiPolynomial_degreeOf {table : MvPolynomial (Fin n) F}
    {columns : Fin M → MvPolynomial (Fin n) F}
    (htable : ∀ v, MvPolynomial.degreeOf v table ≤ 1)
    (hcolumns : ∀ j v, MvPolynomial.degreeOf v (columns j) ≤ 1)
    (xChallenge : F) (j : TermIdx M) (i : Fin n) :
    MvPolynomial.degreeOf i (termPhiPolynomial table columns xChallenge j) ≤ 1 := by
  unfold termPhiPolynomial
  calc
    _ ≤ max (MvPolynomial.degreeOf i (MvPolynomial.C xChallenge))
        (MvPolynomial.degreeOf i
          (match termToInput j with
          | .table => table
          | .column c => columns c)) :=
      MvPolynomial.degreeOf_add_le i _ _
    _ ≤ max 0 1 := by
      gcongr
      · exact (MvPolynomial.degreeOf_C (R := F) xChallenge i).le
      · cases termToInput j with
        | table => exact htable i
        | column c => exact hcolumns c i
    _ = 1 := by omega

theorem termNumeratorPolynomial_degreeOf {multiplicity : MvPolynomial (Fin n) F}
    (hmult : ∀ v, MvPolynomial.degreeOf v multiplicity ≤ 1) (j : TermIdx M) (i : Fin n) :
    MvPolynomial.degreeOf i (termNumeratorPolynomial multiplicity j) ≤ 1 := by
  unfold termNumeratorPolynomial
  cases termToInput j with
  | table => exact hmult i
  | column c => exact (MvPolynomial.degreeOf_C (R := F) (-1 : F) i).le.trans (by omega)

/-- The concrete multivariate LogUp sumcheck polynomial `Q`: the generic batched polynomial
instantiated with the oracle polynomials. -/
noncomputable def logupQPolynomial (groups : Fin K → Finset (TermIdx M))
    (table : MvPolynomial (Fin n) F) (columns : Fin M → MvPolynomial (Fin n) F)
    (multiplicity : MvPolynomial (Fin n) F) (helpers : Fin K → MvPolynomial (Fin n) F)
    (xChallenge : F) (zChallenge : Fin n → F) (batchingScalars : Fin K → F) :
    MvPolynomial (Fin n) F :=
  batchedSumcheckPolynomial groups (termPhiPolynomial table columns xChallenge)
    (termNumeratorPolynomial multiplicity) helpers zChallenge batchingScalars

/-- `Q` has individual degree at most `M + 3`, given that the oracle polynomials are multilinear. -/
theorem logupQPolynomial_degreeOf (groups : Fin K → Finset (TermIdx M))
    {table : MvPolynomial (Fin n) F} {columns : Fin M → MvPolynomial (Fin n) F}
    {multiplicity : MvPolynomial (Fin n) F} {helpers : Fin K → MvPolynomial (Fin n) F}
    (htable : ∀ v, MvPolynomial.degreeOf v table ≤ 1)
    (hcolumns : ∀ j v, MvPolynomial.degreeOf v (columns j) ≤ 1)
    (hmult : ∀ v, MvPolynomial.degreeOf v multiplicity ≤ 1)
    (hhelper : ∀ k v, MvPolynomial.degreeOf v (helpers k) ≤ 1)
    (xChallenge : F) (zChallenge : Fin n → F) (batchingScalars : Fin K → F) (i : Fin n) :
    MvPolynomial.degreeOf i
        (logupQPolynomial groups table columns multiplicity helpers
          xChallenge zChallenge batchingScalars) ≤ M + 3 := by
  refine le_trans (batchedSumcheckPolynomial_degreeOf groups
    (termPhiPolynomial table columns xChallenge) (termNumeratorPolynomial multiplicity)
    helpers zChallenge batchingScalars
    (fun j v => termPhiPolynomial_degreeOf htable hcolumns xChallenge j v)
    (fun j v => termNumeratorPolynomial_degreeOf hmult j v)
    hhelper i) (by omega)

end Polynomial

/-! ## Polynomial evaluation agreement -/

section PolynomialEval

variable {F : Type} [Field F] {n M K : ℕ}

/-- On Boolean rows, the concrete polynomial `Q` agrees with the row-wise LogUp expression built
from the Boolean evaluations of its input polynomials. -/
theorem logupQPolynomial_eval_hypercube (groups : Fin K → Finset (TermIdx M))
    (table : MvPolynomial (Fin n) F) (columns : Fin M → MvPolynomial (Fin n) F)
    (multiplicity : MvPolynomial (Fin n) F) (helpers : Fin K → MvPolynomial (Fin n) F)
    (xChallenge : F) (zChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (u : Fin n → Fin 2) :
    MvPolynomial.eval (u : Fin n → F)
        (logupQPolynomial groups table columns multiplicity helpers
          xChallenge zChallenge batchingScalars)
      =
        qOnHypercube groups (MvPolynomial.toEvalsZeroOne table)
          (fun i => MvPolynomial.toEvalsZeroOne (columns i))
          (MvPolynomial.toEvalsZeroOne multiplicity)
          (fun k => MvPolynomial.toEvalsZeroOne (helpers k))
          xChallenge zChallenge batchingScalars u := by
  have hphi : ∀ i : TermIdx M,
      MvPolynomial.eval (u : Fin n → F) (termPhiPolynomial table columns xChallenge i) =
        termPhi (MvPolynomial.toEvalsZeroOne table)
          (fun j => MvPolynomial.toEvalsZeroOne (columns j)) xChallenge i u := by
    intro i
    unfold termPhiPolynomial termPhi phi
    cases termToInput i <;> simp [MvPolynomial.toEvalsZeroOne]
  have hnum : ∀ i : TermIdx M,
      MvPolynomial.eval (u : Fin n → F) (termNumeratorPolynomial multiplicity i) =
        termNumerator (MvPolynomial.toEvalsZeroOne multiplicity) i u := by
    intro i
    unfold termNumeratorPolynomial termNumerator numerator
    cases termToInput i <;> simp [MvPolynomial.toEvalsZeroOne]
  rw [logupQPolynomial, batchedSumcheckPolynomial, qOnHypercube, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_add, map_mul, map_mul, MvPolynomial.eval_C]
  congr 2
  rw [batchedDomainIdentity, domainIdentityTerm, map_sub, map_mul, map_prod, map_sum]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl (fun i _ => hphi i)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_prod, hnum i]
    congr 1
    exact Finset.prod_congr rfl (fun j _ => hphi j)

/-- At an arbitrary point, the concrete polynomial `Q` agrees with the value reconstructed from
the scalar evaluations of its input polynomials. -/
theorem logupQPolynomial_eval_point (groups : Fin K → Finset (TermIdx M))
    (table : MvPolynomial (Fin n) F) (columns : Fin M → MvPolynomial (Fin n) F)
    (multiplicity : MvPolynomial (Fin n) F) (helpers : Fin K → MvPolynomial (Fin n) F)
    (xChallenge : F) (zChallenge rChallenge : Fin n → F) (batchingScalars : Fin K → F) :
    MvPolynomial.eval rChallenge
        (logupQPolynomial groups table columns multiplicity helpers
          xChallenge zChallenge batchingScalars)
      =
        qAtPoint groups xChallenge zChallenge rChallenge batchingScalars
          (MvPolynomial.eval rChallenge multiplicity)
          (MvPolynomial.eval rChallenge table)
          (fun i => MvPolynomial.eval rChallenge (columns i))
          (fun k => MvPolynomial.eval rChallenge (helpers k)) := by
  have hphi : ∀ i : TermIdx M,
      MvPolynomial.eval rChallenge (termPhiPolynomial table columns xChallenge i) =
        termPhiAtPoint xChallenge (MvPolynomial.eval rChallenge table)
          (fun j => MvPolynomial.eval rChallenge (columns j)) i := by
    intro i
    unfold termPhiPolynomial termPhiAtPoint phiAtPoint
    cases termToInput i <;> simp
  have hnum : ∀ i : TermIdx M,
      MvPolynomial.eval rChallenge (termNumeratorPolynomial multiplicity i) =
        termNumeratorAtPoint (MvPolynomial.eval rChallenge multiplicity) i := by
    intro i
    unfold termNumeratorPolynomial termNumeratorAtPoint numeratorAtPoint
    cases termToInput i <;> simp
  rw [logupQPolynomial, batchedSumcheckPolynomial, qAtPoint, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_add, map_mul, map_mul, MvPolynomial.eval_C]
  congr 2
  rw [batchedDomainIdentity, domainIdentityAtPoint, map_sub, map_mul, map_prod, map_sum]
  congr 1
  · congr 1
    exact Finset.prod_congr rfl (fun i _ => hphi i)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_prod, hnum i]
    congr 1
    exact Finset.prod_congr rfl (fun j _ => hphi j)

end PolynomialEval

end Logup

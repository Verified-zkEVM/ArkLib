/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Logup.Algebra.Lemmas

/-!
# LogUp algebra and sumcheck polynomial

This file exposes the final LogUp polynomial interface used by the protocol: scalar
reconstruction at the final sumcheck point, the concrete multivariate `Q` polynomial, its degree
bound, and the evaluation-agreement lemmas connecting those definitions to the row-wise algebra.

-/

namespace Logup

open scoped BigOperators

section Algebra

variable {F : Type} [Field F] {n M K : ℕ}

/-- The equality-kernel-weighted sum of one group identity is its MLE evaluated at `z`.

This specializes `sum_eqPolynomial_mul_eq_MLE_eval` to the Boolean table of cleared
domain-identity values for group `k`.  It is the algebraic bridge from row-wise outer claims to
point evaluations. -/
theorem domainIdentityKernelClaim_eq_eval_domainIdentityMLE
    (groups : Fin K → Finset (TermIdx M))
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

/-- Good `x` and `z` challenges make the final batching equation nontrivial.

If the cleared lookup identity is nonzero at `x`, the fractional lookup sum is nonzero.  If `z`
does not evaluate any nonzero domain-identity MLE to zero, then either the helper-sum constant term
is already nonzero or some `z`-evaluated group coefficient is nonzero. -/
theorem outer_batch_coefficients_nontrivial_of_good_xz
    (groups : Fin K → Finset (TermIdx M))
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

/-- Deterministic core of outer soundness after all challenges are fixed.

Good `x` makes the rational lookup identity fail, good `z` prevents nonzero group MLEs from being
hidden, and good batching scalars avoid the resulting nontrivial linear equation.  Under those three
conditions, the expanded outer sumcheck claim cannot be zero. -/
theorem outer_linear_claim_ne_zero_of_good_challenges
    (groups : Fin K → Finset (TermIdx M))
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

/-- Lookup containment makes table multiplicities nonzero as field elements.

If a value has nonzero lookup multiplicity and every lookup-column value appears somewhere in the
table, then that value has positive table multiplicity.  The characteristic bound ensures this
positive natural count does not cast to zero in `F`. -/
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

/-- Avoiding table poles is enough to avoid all LogUp denominators under lookup containment.

When every lookup-column value appears in the table, each lookup denominator `x + column j u` is
also some table denominator `x + table v`.  Thus checking table poles rules out both table and
lookup-column denominator zeros. -/
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

/-- There are at most `|H|` outer challenges that make a table denominator vanish.

Each bad challenge is of the form `-table u` for some Boolean row `u`, so the pole set is bounded by
the number of Boolean rows. -/
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

/-- Honest LogUp data makes the row-wise outer sumcheck claim sum to zero.

Assuming lookup containment, nonzero denominator terms, and the characteristic bound needed for
normalized multiplicities, the honest helper values cancel the rational lookup identity.  Therefore
the hypercube sum of `qOnHypercube` is zero for any `z` and batching scalars. -/
theorem logupOuterClaim_zero [Fintype F] [DecidableEq F]
    (groups : Fin K → Finset (TermIdx M))
    (hgroups : ∀ g : TermIdx M → F, (∑ k : Fin K, ∑ i ∈ groups k, g i) = ∑ i : TermIdx M, g i)
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (xChallenge : F) (zChallenge : Fin n → F) (batchingScalars : Fin K → F)
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
  -- Paper eq. (15): the honest identity at `xChallenge`, as the evaluated forward of Lemma 5
  -- (`setInclusion_eval_forward`) with the lookup columns as `a` and the table as `b`.
  have hmi : (∑ u : Fin n → Fin 2,
        normalizedMultiplicityValue table columns u / (xChallenge + table u))
      = ∑ j : Fin M, ∑ u : Fin n → Fin 2, (1 : F) / (xChallenge + columns j u) := by
    have h := setInclusion_eval_forward (fun p : Fin M × (Fin n → Fin 2) => columns p.1 p.2)
      table xChallenge hchar
    rw [Fintype.sum_prod_type] at h
    exact h.symm
  simp_rw [hq, hsum, hterm]
  rw [Finset.sum_add_distrib, hmi,
    Finset.sum_comm (f := fun u j => (-1 : F) / (xChallenge + columns j u)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun u _ => by ring)

end Algebra
/-! ## Final-point reconstructions

The final LogUp verifier does not evaluate the whole polynomial `Q` directly.  Instead, after
sumcheck fixes a point `r`, it receives scalar openings such as `m(r)`, `table(r)`,
`column_i(r)`, and `helper_k(r)`.  This section defines the scalar expression reconstructed from
those openings, mirroring the row-wise definitions above but with field elements instead of
Boolean-row functions. -/

section AtPoint

variable {F : Type} [Field F] {n M K : ℕ}

/-- The denominator value for a table or lookup-column term at the final sumcheck point.

The table term uses `x + table(r)`, while lookup-column term `i` uses `x + column_i(r)`. -/
def phiAtPoint (xChallenge tVal : F) (colVals : Fin M → F) : InputIdx M → F
  | .table => xChallenge + tVal
  | .column i => xChallenge + colVals i

/-- The numerator value for a table or lookup-column term at the final sumcheck point.

The table term uses the opened multiplicity `m(r)`, while lookup-column terms still contribute
`-1`. -/
def numeratorAtPoint (mVal : F) : InputIdx M → F
  | .table => mVal
  | .column _ => -1

/-- The final-point denominator value using the paper's numeric term index `0, ..., M`. -/
def termPhiAtPoint (xChallenge tVal : F) (colVals : Fin M → F) (i : TermIdx M) : F :=
  phiAtPoint xChallenge tVal colVals (termToInput i)

/-- The final-point numerator value using the paper's numeric term index `0, ..., M`. -/
def termNumeratorAtPoint (mVal : F) (i : TermIdx M) : F :=
  numeratorAtPoint mVal (termToInput i)

/-- The cleared helper equation reconstructed from scalar openings at the final point.

This is the point-value analogue of `domainIdentityTerm`: it checks whether the opened helper value
for group `k` is consistent with the opened table, column, and multiplicity values after clearing
denominators. -/
noncomputable def domainIdentityAtPoint (groups : Fin K → Finset (TermIdx M))
    (xChallenge mVal tVal : F) (colVals : Fin M → F) (helperVals : Fin K → F) (k : Fin K) : F :=
  helperVals k * (∏ i ∈ groups k, termPhiAtPoint xChallenge tVal colVals i) -
    ∑ i ∈ groups k,
      termNumeratorAtPoint mVal i *
        ∏ j ∈ (groups k).erase i, termPhiAtPoint xChallenge tVal colVals j

/-- The scalar value of `Q` reconstructed by the final verifier from oracle openings.

This is paper equation (19): the verifier combines opened helpers, final-point denominators,
final-point numerators, the equality-kernel value at `(r, z)`, and batching scalars to reproduce
what `logupQPolynomial` should evaluate to at `r`. -/
noncomputable def qAtPoint (groups : Fin K → Finset (TermIdx M))
    (xChallenge : F) (zChallenge rChallenge : Fin n → F) (batchingScalars : Fin K → F)
    (mVal tVal : F) (colVals : Fin M → F) (helperVals : Fin K → F) : F :=
  ∑ k : Fin K, (
    helperVals k +
      MvPolynomial.eval rChallenge (MvPolynomial.eqPolynomial zChallenge) * batchingScalars k *
        domainIdentityAtPoint groups xChallenge mVal tVal colVals helperVals k)

end AtPoint

/-! ## The LogUp polynomial

This section instantiates the generic batched polynomial with LogUp's actual oracle polynomials:
the table polynomial, lookup-column polynomials, multiplicity polynomial, and helper polynomials.
The resulting `logupQPolynomial` is the polynomial committed to the embedded sumcheck protocol, and
the degree lemmas here provide the individual-degree bound required by sumcheck. -/

section Polynomial

variable {F : Type} [Field F] {n M K : ℕ}

/-- The denominator polynomial for one LogUp term.

For the table term this is `x + table`; for a lookup-column term it is `x + column_i`.  It is the
polynomial analogue of `termPhi`. -/
noncomputable def termPhiPolynomial (table : MvPolynomial (Fin n) F)
    (columns : Fin M → MvPolynomial (Fin n) F) (xChallenge : F) (i : TermIdx M) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C xChallenge +
    match termToInput i with
    | .table => table
    | .column j => columns j

/-- The numerator polynomial for one LogUp term.

The table term uses the multiplicity polynomial, while lookup-column terms are the constant
polynomial `-1`.  It is the polynomial analogue of `termNumerator`. -/
noncomputable def termNumeratorPolynomial (multiplicity : MvPolynomial (Fin n) F) (i : TermIdx M) :
    MvPolynomial (Fin n) F :=
  match termToInput i with
  | .table => multiplicity
  | .column _ => MvPolynomial.C (-1)

/-- Denominator polynomials are multilinear when the table and column polynomials are multilinear.

Adding the scalar challenge `x` does not increase individual degree, so every variable still has
degree at most one. -/
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

/-- Numerator polynomials are multilinear when the multiplicity polynomial is multilinear.

The table numerator inherits the multiplicity degree bound; lookup-column numerators are constants,
so their individual degree is zero. -/
theorem termNumeratorPolynomial_degreeOf {multiplicity : MvPolynomial (Fin n) F}
    (hmult : ∀ v, MvPolynomial.degreeOf v multiplicity ≤ 1) (j : TermIdx M) (i : Fin n) :
    MvPolynomial.degreeOf i (termNumeratorPolynomial multiplicity j) ≤ 1 := by
  unfold termNumeratorPolynomial
  cases termToInput j with
  | table => exact hmult i
  | column c => exact (MvPolynomial.degreeOf_C (R := F) (-1 : F) i).le.trans (by omega)

/-- The concrete multivariate LogUp polynomial sent to sumcheck.

This instantiates `batchedSumcheckPolynomial` with LogUp denominator polynomials, numerator
polynomials, helper polynomials, the equality-kernel challenge `z`, and batching scalars. -/
noncomputable def logupQPolynomial (groups : Fin K → Finset (TermIdx M))
    (table : MvPolynomial (Fin n) F) (columns : Fin M → MvPolynomial (Fin n) F)
    (multiplicity : MvPolynomial (Fin n) F) (helpers : Fin K → MvPolynomial (Fin n) F)
    (xChallenge : F) (zChallenge : Fin n → F) (batchingScalars : Fin K → F) :
    MvPolynomial (Fin n) F :=
  batchedSumcheckPolynomial groups (termPhiPolynomial table columns xChallenge)
    (termNumeratorPolynomial multiplicity) helpers zChallenge batchingScalars

/-- `logupQPolynomial` has the individual-degree bound required by the embedded sumcheck.

If every oracle polynomial is multilinear, then the generic batched-polynomial degree bound applies
with `T = M + 1`, giving individual degree at most `M + 3`. -/
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

/-! ## Polynomial evaluation agreement

These lemmas connect the three views of the same LogUp expression.  On Boolean rows,
`logupQPolynomial` evaluates to the semantic row-wise expression `qOnHypercube`.  At an arbitrary
field point, it evaluates to the scalar reconstruction `qAtPoint` used by the final verifier. -/

section PolynomialEval

variable {F : Type} [Field F] {n M K : ℕ}

/-- On Boolean rows, `logupQPolynomial` agrees with the row-wise LogUp expression.

Evaluating the polynomial inputs on a Boolean row turns denominator polynomials into `termPhi`,
numerator polynomials into `termNumerator`, and the generic batched polynomial into
`qOnHypercube`.  This is the bridge used by completeness to relate honest polynomial data to the
hypercube sum. -/
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

/-- At any field point, `logupQPolynomial` agrees with the final verifier's scalar reconstruction.

After the verifier receives openings of the multiplicity, table, column, and helper polynomials at
`rChallenge`, this lemma says that `qAtPoint` computes the same value as directly evaluating
`logupQPolynomial` at `rChallenge`. -/
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

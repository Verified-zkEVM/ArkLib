/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.MvPolynomial.Multilinear
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.DeriveFintype

/-!
# LogUp algebra and sumcheck polynomial

This file contains the protocol-independent algebra behind the LogUp lookup argument.  The
definitions are phrased in terms of plain Boolean-hypercube functions, multivariate polynomials,
field challenges, and groups of fractional terms, rather than verifier/prover states or oracle
transcripts.

-/

namespace Logup

open scoped BigOperators

/-! ## Generic batched polynomial

This section isolates the polynomial shape used for a batched sumcheck claim.  It does not mention
LogUp-specific table or lookup data: each term has an abstract denominator polynomial, numerator
polynomial, and helper polynomial.  The degree lemmas here say that once those ingredients are
multilinear, batching the cleared identities with an equality kernel only raises the individual
degree in the expected way. -/

section BatchedPolynomial

variable {F : Type} [Field F] {n T K : ℕ}
variable (groups : Fin K → Finset (Fin T))
variable (phiPoly numerPoly : Fin T → MvPolynomial (Fin n) F)
variable (helperPoly : Fin K → MvPolynomial (Fin n) F)

/-- The cleared-denominator identity for one group of fractional terms.

For a group `k`, this is the polynomial form of
`helper = sum_i numerator_i / denominator_i` after multiplying by the product of all denominators in
that group.  It is abstract in the sense that the denominator, numerator, and helper polynomials are
parameters; LogUp instantiates them later. -/
noncomputable def batchedDomainIdentity (k : Fin K) : MvPolynomial (Fin n) F :=
  helperPoly k * (∏ i ∈ groups k, phiPoly i) -
    ∑ i ∈ groups k, numerPoly i * ∏ j ∈ (groups k).erase i, phiPoly j

/-- The generic polynomial whose Boolean-hypercube sum is checked by sumcheck.

The first summand asks that the helpers themselves sum to zero.  The second summand batches every
group's cleared-denominator identity using the equality kernel at `zChallenge` and the random
batching scalars.  This is the protocol-free shape later instantiated by `logupQPolynomial`. -/
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

/-- A cleared identity over at most `T` fractional terms has individual degree at most `T + 1`.

The extra `+ 1` comes from the helper or numerator factor.  This lemma is the local degree bound
used before the equality kernel and random batching scalar are added. -/
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

/-- The generic batched sumcheck polynomial has individual degree at most `T + 2`.

Compared with a single cleared identity, batching adds one equality-kernel factor, which
contributes one more degree in each variable.  Constants such as the batching scalars do not affect
the bound. -/
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

LogUp's rational identity has `M + 1` fractional terms.  The paper indexes them by numbers:
term `0` is the table term and terms `1, ..., M` are lookup-column terms.  The protocol code often
uses the semantic labels `table` and `column i`; this section provides the conversions and proves
they are inverse to each other. -/

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

/-! ## Fractional decompositions in `F[X]` (paper Section 2.3)

This section formalizes the paper's univariate logarithmic-derivative facts without using rational
functions.  Instead, every identity is multiplied by the common denominator
`prod_w (X + w)` and expressed as a polynomial identity in `F[X]`.

The key idea is that the cleared numerator remembers the multiplicity function. This gives a
polynomial proof of uniqueness for fractional decompositions, a bridge from indexed sums to
value-multiplicity sums, and the set-inclusion criterion used by LogUp completeness and soundness.-/

section FractionalDecomposition

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The cleared-denominator decomposition `∑_{z ∈ F} m(z) · ∏_{w ≠ z}(X + w)` in `F[X]`: the
numerator left after multiplying the formal `∑_z m(z)/(X + z)` by `∏_{w∈F}(X + w)`. -/
noncomputable def clearedDecomp (m : F → F) : F[X] :=
  ∑ z : F, C (m z) * ∏ w ∈ Finset.univ.erase z, (X + C w)

/-- **Lemma 4** (uniqueness of fractional decompositions). Over a finite field the coefficient map
`m ↦ clearedDecomp m` is injective: two cleared decompositions coincide in `F[X]` iff their
coefficient functions agree everywhere. -/
theorem clearedDecomp_injective {m₁ m₂ : F → F} :
    clearedDecomp m₁ = clearedDecomp m₂ ↔ m₁ = m₂ := by
  refine ⟨fun H => ?_, fun H => by rw [H]⟩
  funext w
  -- The coefficient-difference decomposition is the zero polynomial.
  have hp0 : (∑ z : F, C (m₁ z - m₂ z) * ∏ u ∈ Finset.univ.erase z, (X + C u)) = 0 := by
    have hsub : clearedDecomp m₁ - clearedDecomp m₂ = 0 := by rw [H, sub_self]
    rw [clearedDecomp, clearedDecomp, ← Finset.sum_sub_distrib] at hsub
    rw [← hsub]
    exact Finset.sum_congr rfl (fun z _ => by rw [map_sub, sub_mul])
  -- Evaluating at `-w` isolates the `w`-th coefficient.
  have heval := congrArg (Polynomial.eval (-w)) hp0
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_zero] at heval
  have hsingle : (∑ z : F, (m₁ z - m₂ z) * ∏ u ∈ Finset.univ.erase z, (-w + u))
      = (m₁ w - m₂ w) * ∏ u ∈ Finset.univ.erase w, (-w + u) := by
    refine Finset.sum_eq_single w (fun z _ hzw => ?_)
      (fun h => absurd (Finset.mem_univ w) h)
    have hwmem : w ∈ Finset.univ.erase z :=
      Finset.mem_erase.mpr ⟨fun hwz => hzw hwz.symm, Finset.mem_univ w⟩
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero hwmem (neg_add_cancel w))
  rw [hsingle] at heval
  have hprodne : (∏ u ∈ Finset.univ.erase w, (-w + u)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro u hu hzero
    rw [Finset.mem_erase] at hu
    exact hu.1 (neg_injective (add_eq_zero_iff_eq_neg.mp hzero)).symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp heval).resolve_right hprodne)

/-- "Collecting": an indexed sum of cleared single terms `∑ i, c i · ∏_{w ≠ a i}(X + w)` equals the
cleared decomposition whose coefficient at `z` is the total weight `∑_{a i = z} c i`. This is the
bridge between sequence-indexed sums (the protocol side) and `clearedDecomp` (Lemmas 4/5). -/
theorem clearedSum_eq_clearedDecomp {ι : Type*} [Fintype ι] (a c : ι → F) :
    (∑ i, C (c i) * ∏ w ∈ Finset.univ.erase (a i), (X + C w))
      = clearedDecomp (fun z => ∑ i ∈ Finset.univ.filter (fun i => a i = z), c i) := by
  unfold clearedDecomp
  rw [← Finset.sum_fiberwise (Finset.univ : Finset ι) a
        (fun i => C (c i) * ∏ w ∈ Finset.univ.erase (a i), (X + C w))]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_filter] at hi
  rw [hi.2]

/-- The multiplicity of a value `z` in a finite sequence `a : ι → F`. -/
def seqMultiplicity {ι : Type*} [Fintype ι] (a : ι → F) (z : F) : ℕ :=
  (Finset.univ.filter fun i => a i = z).card

/-- **Lemma 5** (set inclusion), cleared-denominator form. When the field characteristic exceeds the
sizes of the index types, the set underlying `a` is contained in that of `b` iff there exist
multiplicities `m` making the cleared logarithmic-derivative identity hold in `F[X]` (the cleared
form of `∑_i 1/(X + a i) = ∑_j m j/(X + b j)`). The honest witness is the normalized multiplicity
`m j = ma(b j)/mb(b j)`. Generalizes the paper's equal-length sequences to arbitrary index types.
This theorem is kept as a faithful statement of Lemma 5; the later security proofs use evaluated
and contrapositive specializations instead. -/
theorem setInclusion_iff_cleared {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hNa : Fintype.card ι < ringChar F) (hNb : Fintype.card κ < ringChar F)
    (a : ι → F) (b : κ → F) :
    (∀ i, ∃ j, a i = b j) ↔
      ∃ m : κ → F,
        (∑ i, ∏ w ∈ Finset.univ.erase (a i), (X + C w))
          = ∑ j, C (m j) * ∏ w ∈ Finset.univ.erase (b j), (X + C w) := by
  -- Nonzero-cast of multiplicities: any count below `ringChar F` survives.
  have hcastne : ∀ k : ℕ, 0 < k → k < ringChar F → (k : F) ≠ 0 := by
    intro k hk hkr hzero
    exact (Nat.not_dvd_of_pos_of_lt hk hkr) ((ringChar.spec F k).1 hzero)
  have hleA : ∀ w : F, seqMultiplicity a w ≤ Fintype.card ι := by
    intro w
    calc seqMultiplicity a w ≤ (Finset.univ : Finset ι).card := Finset.card_filter_le _ _
      _ = Fintype.card ι := Finset.card_univ
  have hleB : ∀ w : F, seqMultiplicity b w ≤ Fintype.card κ := by
    intro w
    calc seqMultiplicity b w ≤ (Finset.univ : Finset κ).card := Finset.card_filter_le _ _
      _ = Fintype.card κ := Finset.card_univ
  have hcast : ∀ z : F, (∑ _i ∈ Finset.univ.filter (fun i => a i = z), (1 : F))
      = (seqMultiplicity a z : F) := by
    intro z; rw [Finset.sum_const, nsmul_eq_mul, mul_one]; rfl
  -- Collecting turns each side into a `clearedDecomp`.
  have hL : (∑ i, ∏ w ∈ Finset.univ.erase (a i), (X + C w))
      = clearedDecomp (fun z => (seqMultiplicity a z : F)) := by
    have h1 : (∑ i, ∏ w ∈ Finset.univ.erase (a i), (X + C w))
        = ∑ i, C (1 : F) * ∏ w ∈ Finset.univ.erase (a i), (X + C w) := by simp
    rw [h1, clearedSum_eq_clearedDecomp a (fun _ => 1)]
    exact congrArg clearedDecomp (funext (fun z => hcast z))
  have hR : ∀ m : κ → F, (∑ j, C (m j) * ∏ w ∈ Finset.univ.erase (b j), (X + C w))
      = clearedDecomp (fun z => ∑ j ∈ Finset.univ.filter (fun j => b j = z), m j) :=
    fun m => clearedSum_eq_clearedDecomp b m
  -- By Lemma 4 the identity is exactly fiberwise equality of total weights.
  have key : ∀ m : κ → F,
      ((∑ i, ∏ w ∈ Finset.univ.erase (a i), (X + C w))
          = ∑ j, C (m j) * ∏ w ∈ Finset.univ.erase (b j), (X + C w))
        ↔ ∀ z : F, (seqMultiplicity a z : F)
            = ∑ j ∈ Finset.univ.filter (fun j => b j = z), m j := by
    intro m
    rw [hL, hR m, clearedDecomp_injective]
    exact funext_iff
  constructor
  · -- Forward: the normalized multiplicity is a valid witness.
    intro hinc
    refine ⟨fun j => (seqMultiplicity a (b j) : F) / (seqMultiplicity b (b j) : F), (key _).2 ?_⟩
    intro z
    by_cases hz : seqMultiplicity a z = 0
    · rw [hz, Nat.cast_zero]
      symm
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_filter] at hj
      rw [hj.2, hz, Nat.cast_zero, zero_div]
    · obtain ⟨i₀, hi₀⟩ :=
        Finset.card_ne_zero.mp (show (Finset.univ.filter (fun i => a i = z)).card ≠ 0 from hz)
      rw [Finset.mem_filter] at hi₀
      obtain ⟨j₀, hj₀⟩ := hinc i₀
      have hbz_ne : seqMultiplicity b z ≠ 0 := by
        refine Finset.card_ne_zero.mpr ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, ?_⟩⟩
        rw [hj₀.symm.trans hi₀.2]
      have hconst : ∀ j ∈ Finset.univ.filter (fun j => b j = z),
          (seqMultiplicity a (b j) : F) / (seqMultiplicity b (b j) : F)
            = (seqMultiplicity a z : F) / (seqMultiplicity b z : F) := by
        intro j hj; rw [Finset.mem_filter] at hj; rw [hj.2]
      have hcard : ((Finset.univ.filter (fun j => b j = z)).card : F) = (seqMultiplicity b z : F) :=
        rfl
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hcard]
      have hbzF : (seqMultiplicity b z : F) ≠ 0 :=
        hcastne _ (Nat.pos_of_ne_zero hbz_ne) (lt_of_le_of_lt (hleB z) hNb)
      field_simp
  · -- Converse: a value of `a` has nonzero multiplicity, so its fiber in `b` is nonempty.
    rintro ⟨m, hm⟩ i
    have hcoef := (key m).1 hm (a i)
    by_contra hcon
    simp only [not_exists] at hcon
    have hempty : Finset.univ.filter (fun j => b j = a i) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      exact fun j _ hbj => hcon j hbj.symm
    rw [hempty, Finset.sum_empty] at hcoef
    have hpos : 0 < seqMultiplicity a (a i) :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
    exact hcastne _ hpos (lt_of_le_of_lt (hleA (a i)) hNa) hcoef

set_option linter.unusedFintypeInType false in
/-- **Lemma 5**, forward direction evaluated at a point `x` (paper eq. (15)). If every value of `a`
occurs among the values of `b`, then the logarithmic-derivative identity holds at `x` with the
normalized multiplicity `seqMultiplicity a (b j) / seqMultiplicity b (b j)` as witness. This is the
evaluated specialization that the completeness proof consumes; the formal `F[X]` statement is
`setInclusion_iff_cleared`. The hypothesis `hchar` (that a nonzero `a`-multiplicity forces a nonzero
`b`-multiplicity in `F`) packages set inclusion together with the characteristic bound, exactly as
in the protocol. Lean's `_ / 0 = 0` convention makes pole hypotheses unnecessary. -/
theorem setInclusion_eval_forward {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → F) (b : κ → F) (x : F)
    (hchar : ∀ z : F, seqMultiplicity a z ≠ 0 → (seqMultiplicity b z : F) ≠ 0) :
    (∑ i, (1 : F) / (x + a i))
      = ∑ j, (seqMultiplicity a (b j) : F) / (seqMultiplicity b (b j) : F) / (x + b j) := by
  have key : ∀ z : F,
      seqMultiplicity b z • ((seqMultiplicity a z : F) / (seqMultiplicity b z : F) / (x + z))
        = seqMultiplicity a z • ((1 : F) / (x + z)) := by
    intro z
    by_cases ha : seqMultiplicity a z = 0
    · simp [ha]
    · rw [nsmul_eq_mul, nsmul_eq_mul]
      have hbF : (seqMultiplicity b z : F) ≠ 0 := hchar z ha
      field_simp
  have hLHS : (∑ i, (1 : F) / (x + a i))
      = ∑ z : F, seqMultiplicity a z • ((1 : F) / (x + z)) := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset ι) a]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    have h : ∀ i ∈ Finset.univ.filter (fun i => a i = z),
        (1 : F) / (x + a i) = (1 : F) / (x + z) :=
      fun i hi => by rw [Finset.mem_filter] at hi; rw [hi.2]
    rw [Finset.sum_congr rfl h, Finset.sum_const]
    rfl
  have hRHS : (∑ j, (seqMultiplicity a (b j) : F) / (seqMultiplicity b (b j) : F) / (x + b j))
      = ∑ z : F, seqMultiplicity b z •
          ((seqMultiplicity a z : F) / (seqMultiplicity b z : F) / (x + z)) := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset κ) b]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    have h : ∀ j ∈ Finset.univ.filter (fun j => b j = z),
        (seqMultiplicity a (b j) : F) / (seqMultiplicity b (b j) : F) / (x + b j)
          = (seqMultiplicity a z : F) / (seqMultiplicity b z : F) / (x + z) :=
      fun j hj => by rw [Finset.mem_filter] at hj; rw [hj.2]
    rw [Finset.sum_congr rfl h, Finset.sum_const]
    rfl
  rw [hLHS, hRHS]
  exact Finset.sum_congr rfl (fun z _ => (key z).symm)

end FractionalDecomposition

/-! ## Fractional-identity algebra

This section turns LogUp's lookup condition into row-wise algebra over the Boolean hypercube.  The
table, lookup columns, multiplicity, and helpers are plain functions `(Fin n -> Fin 2) -> F`; no
oracle statements or protocol transcripts appear here.

The definitions describe the denominator occurrences, the cleared univariate identity in the outer
challenge `x`, the helper equations for grouped terms, and the Boolean-row expression `qOnHypercube`
that will later be lifted into the polynomial sent to sumcheck. -/

section Algebra

variable {F : Type} [Field F] {n M K : ℕ}

/-- Number of table rows with value `a`. -/
def tableMultiplicityCount [Fintype F] [DecidableEq F] (table : (Fin n → Fin 2) → F) (a : F) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 2)).filter fun u => table u = a).card

/-- Total number of lookup-column entries with value `a`. -/
def lookupMultiplicityCount [Fintype F] [DecidableEq F]
    (columns : Fin M → (Fin n → Fin 2) → F) (a : F) : ℕ :=
  ((Finset.univ : Finset (Fin M × (Fin n → Fin 2))).filter fun ix => columns ix.1 ix.2 = a).card

/-! ### Cleared occurrence identities

The LogUp rational identity has one denominator for each table row and each lookup-column row.
Multiplying by the product of all denominators gives a single univariate polynomial in the outer
challenge `x`.  The lemmas below explain when that cleared polynomial is nonzero, how large its bad
root/pole sets can be, and how to translate between table/column occurrences and grouped term
indices. -/

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

/-- The key repeated-pole coefficient calculation. After shifting by a value `z`, the coefficient
of the first possible power of `X` in the cleared occurrence polynomial is the total coefficient
on the `z`-fiber, times the nonzero product of the other shifted values. -/
theorem clearedOccurrences_taylor_coeff_fiber_pred
    {α : Type} [Fintype α] [DecidableEq α] [DecidableEq F]
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

/-- If the total coefficient on one denominator-value fiber is nonzero, then the cleared
occurrence polynomial cannot vanish, even when the denominator value occurs repeatedly. -/
theorem clearedOccurrences_ne_zero_of_fiber_sum_ne_zero
    {α : Type} [Fintype α] [DecidableEq α] [DecidableEq F]
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

/-- If a value is missing from the table, its `LookupOccur` numerator fiber sum is the negative
lookup multiplicity. -/
theorem lookupOccurNumerator_fiber_sum_of_table_missing
    [Fintype F] [DecidableEq F]
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

omit [Field F] in
/-- The multiplicity count of an actually occurring lookup-column value is positive. -/
theorem lookupMultiplicityCount_pos_of_column_value [Fintype F] [DecidableEq F]
    (columns : Fin M → (Fin n → Fin 2) → F) (i : Fin M) (u : Fin n → Fin 2) :
    0 < lookupMultiplicityCount columns (columns i u) := by
  rw [lookupMultiplicityCount, Finset.card_pos]
  exact ⟨(i, u), by simp⟩

omit [Field F] in
/-- A value absent from the table has table multiplicity zero. -/
theorem tableMultiplicityCount_eq_zero_of_missing [Fintype F] [DecidableEq F]
    (table : (Fin n → Fin 2) → F) {a : F} (hmissing : ∀ u, a ≠ table u) :
    tableMultiplicityCount table a = 0 := by
  rw [tableMultiplicityCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro u _ hu
  exact hmissing u hu.symm

/-- Under the LogUp characteristic bound, a positive lookup multiplicity remains nonzero in `F`. -/
theorem lookupMultiplicityCount_cast_ne_zero_of_pos [Fintype F] [DecidableEq F]
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

/-- Root-count form of the previous two lemmas, restricted to non-pole challenges. -/
theorem clearedLookupIdentity_bad_x_card_le [Fintype F] [DecidableEq F]
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

/-- The set of denominator-pole challenges for all table and column occurrences has size at most
the number of occurrences. -/
theorem lookupOccur_pole_card_le [Fintype F] [DecidableEq F]
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

/-- Root-count bound for the cleared lookup identity over all field challenges. -/
theorem clearedLookupIdentity_root_card_le [Fintype F] [DecidableEq F]
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

/-- The honest table multiplicity value used in the LogUp identity at one Boolean row.

For a table value `a = table u`, this is `lookup_count(a) / table_count(a)`.  Under the lookup
containment assumptions used elsewhere, it is the normalized multiplicity assigned to row `u` in
paper equation (14). -/
noncomputable def normalizedMultiplicityValue [Fintype F] [DecidableEq F]
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F) (u : Fin n → Fin 2) : F :=
  let a := table u
  (lookupMultiplicityCount columns a : F) / (tableMultiplicityCount table a : F)

/-- The denominator function for a table or lookup-column term at a Boolean row.

The table term uses `x + table u`; a lookup-column term `i` uses `x + columns i u`.  These are the
`phi_i(u)` denominators of LogUp's logarithmic-derivative identity. -/
noncomputable def phi (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (xChallenge : F) : InputIdx M → (Fin n → Fin 2) → F
  | .table => fun u => xChallenge + table u
  | .column i => fun u => xChallenge + columns i u

/-- The numerator function for a table or lookup-column term at a Boolean row.

The table term contributes the claimed multiplicity `m(u)`, while every lookup-column term
contributes `-1`.  This is the signed numerator convention used in the rational lookup identity. -/
noncomputable def numerator (multiplicity : (Fin n → Fin 2) → F) :
    InputIdx M → (Fin n → Fin 2) → F
  | .table => multiplicity
  | .column _ => fun _ => -1

/-- The denominator `phi_i(u)` using the paper's numeric term index `i : TermIdx M`.

This is the same data as `phi`, but with term `0` representing the table and positive terms
representing lookup columns. -/
noncomputable def termPhi (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (xChallenge : F) (i : TermIdx M) (u : Fin n → Fin 2) : F :=
  phi table columns xChallenge (termToInput i) u

/-- The signed numerator `m_i(u)` using the paper's numeric term index `i : TermIdx M`.

Term `0` returns the multiplicity value, while lookup-column terms return `-1`. -/
noncomputable def termNumerator (multiplicity : (Fin n → Fin 2) → F)
    (i : TermIdx M) (u : Fin n → Fin 2) : F :=
  numerator multiplicity (termToInput i) u

/-- The cleared helper equation for one group of LogUp terms at one Boolean row.

For group `k`, the intended equation is
`helpers k u = sum_{i in group k} termNumerator i u / termPhi i u`.  This definition multiplies by
the product of denominators in the group, so it is meaningful even as a polynomial identity.  A
value of zero means the helper is consistent with that group's fractional sum. -/
noncomputable def domainIdentityTerm (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (k : Fin K) (u : Fin n → Fin 2) : F :=
  helpers k u * (∏ i ∈ groups k, termPhi table columns xChallenge i u) -
    ∑ i ∈ groups k, termNumerator multiplicity i u * ∏ j
        ∈ (groups k).erase i, termPhi table columns xChallenge j u

/-- The fractional helper value expected for one group at one Boolean row.

This is the right-hand side of paper equation (16): the sum of signed numerators divided by
denominators over all terms assigned to group `k`. -/
noncomputable def helperValue (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F) (xChallenge : F) (k : Fin K) (u : Fin n → Fin 2) : F :=
  ∑ i ∈ groups k, termNumerator multiplicity i u / termPhi table columns xChallenge i u

/-- The row-wise value of the LogUp polynomial `Q` before it is represented as an MvPolynomial.

At each Boolean row, `Q` adds the helper value and a batched, equality-kernel-weighted cleared
domain identity for every group.  Summing this over the hypercube gives the outer sumcheck claim. -/
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

/-- If a helper is exactly its fractional group sum, the corresponding cleared identity is zero.

The nonzero-denominator hypothesis lets us multiply the fractional helper equation by the product
of all denominators in the group.  This is the row-wise algebra behind honest helper correctness. -/
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

/-- Away from denominator poles, the cleared lookup polynomial evaluates to denominator product
times the original fractional lookup sum.

This connects the univariate polynomial `clearedLookupIdentity` back to the rational identity from
the paper: if no denominator `x + value` is zero, then clearing denominators is reversible. -/
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

/-- A nonzero cleared lookup evaluation implies a nonzero fractional lookup sum, provided no
denominator vanishes.

This is the soundness-facing contrapositive of denominator clearing: if the common-denominator
product is nonzero and the cleared polynomial is nonzero at `x`, then the rational lookup identity
also fails at `x`. -/
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

/-- A zero cleared domain identity forces the helper to equal its fractional group sum.

This is the converse of `domainIdentityTerm_eq_zero` under nonzero denominators.  It lets later
proofs recover the intended helper equation from the cleared polynomial equation. -/
theorem helper_eq_helperValue_of_domainIdentityTerm_eq_zero
    (groups : Fin K → Finset (TermIdx M))
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

/-- Convert a numeric LogUp term and Boolean row into the matching table/column occurrence.

This is the bridge between grouped term sums (`TermIdx M`) and the flattened occurrence type used
by the cleared univariate lookup identity. -/
def termLookupOccur {n M : ℕ} (i : TermIdx M) (u : Fin n → Fin 2) : LookupOccur n M :=
  match termToInput i with
  | .table => .table u
  | .column j => .column j u

/-- The pair of a term index and Boolean row is equivalent to a denominator occurrence.

This equivalence justifies rewriting sums over all table/column occurrences as row-by-row sums over
all LogUp terms. -/
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

/-- The numerator attached to a converted term occurrence is the term numerator. -/
@[simp]
theorem lookupOccurNumerator_termLookupOccur
    (multiplicity : (Fin n → Fin 2) → F) (i : TermIdx M) (u : Fin n → Fin 2) :
    lookupOccurNumerator multiplicity (termLookupOccur i u) =
      termNumerator multiplicity i u := by
  unfold termLookupOccur termNumerator numerator lookupOccurNumerator
  cases termToInput i <;> rfl

/-- The denominator attached to a converted term occurrence is the term denominator. -/
@[simp]
theorem add_lookupOccurValue_termLookupOccur
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (xChallenge : F) (i : TermIdx M) (u : Fin n → Fin 2) :
    xChallenge + lookupOccurValue table columns (termLookupOccur i u) =
      termPhi table columns xChallenge i u := by
  unfold termLookupOccur termPhi phi lookupOccurValue
  cases termToInput i <;> rfl

/-- The global fractional lookup sum can be written row-by-row over numeric LogUp terms.

The left side sums over flattened table/column occurrences.  The right side first chooses a Boolean
row and then sums over the paper's term indices `0, ..., M`.  This is the bookkeeping bridge needed
to compare the cleared lookup identity with grouped helper sums. -/
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

/-- One coordinate factor of the Boolean equality polynomial has total degree at most one.

This local degree fact is used to show that equality kernels and multilinear extensions have total
degree at most the number of variables. -/
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

/-- The Boolean equality polynomial in `n` variables has total degree at most `n`.

It is a product of one degree-one factor per coordinate, so this is the total-degree version of
multilinearity for `MvPolynomial.eqPolynomial`. -/
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

/-- The multilinear extension of any Boolean-hypercube table has total degree at most `n`.

`MvPolynomial.MLE` is a linear combination of equality polynomials, one for each Boolean row, so it
inherits the same total-degree bound. -/
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

/-- Pairing Boolean evaluations with the equality kernel evaluates the multilinear extension.

The sum `sum_u eq_z(u) * evals u` is exactly `MLE evals` evaluated at `z`.  This is the algebraic
reason the verifier's Lagrange-kernel query corresponds to a point evaluation. -/
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

/-- The multilinear extension of one group's cleared domain-identity values.

For fixed table, columns, multiplicity, helpers, and `x`, this polynomial extends the Boolean table
`u ↦ domainIdentityTerm ... k u` from the hypercube to all field points. -/
noncomputable def domainIdentityMLE
    (groups : Fin K → Finset (TermIdx M))
    (table : (Fin n → Fin 2) → F) (columns : Fin M → (Fin n → Fin 2) → F)
    (multiplicity : (Fin n → Fin 2) → F)
    (helpers : Fin K → (Fin n → Fin 2) → F)
    (xChallenge : F) (k : Fin K) : MvPolynomial (Fin n) F :=
  MvPolynomial.MLE
    (fun u => domainIdentityTerm groups table columns multiplicity helpers xChallenge k u)

/-- If a group's domain-identity MLE is the zero polynomial, every Boolean-row identity vanishes.

The proof evaluates the zero polynomial at a Boolean point.  This lets later arguments turn a
polynomial zero statement back into row-wise helper equations. -/
theorem domainIdentityTerm_eq_zero_of_domainIdentityMLE_eq_zero
    (groups : Fin K → Finset (TermIdx M))
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

/-- If all group MLEs are zero, the total helper sum equals the global fractional lookup sum.

Zero MLEs give zero cleared identities on every Boolean row.  Away from denominator poles, those
cleared identities force each helper to equal its fractional group sum; summing over groups and rows
then reconstructs the flattened occurrence sum from `clearedLookupIdentity`. -/
theorem helperSum_eq_lookupOccur_fractionalSum_of_domainIdentityMLEs_zero
    (groups : Fin K → Finset (TermIdx M))
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

/-- If helpers sum to zero while the fractional lookup sum is nonzero, some group MLE is nonzero.

This is the deterministic source of the bad-`z` event in soundness.  If every group MLE were zero,
the previous lemma would force the helper sum and fractional lookup sum to be equal, contradicting
the hypotheses. -/
theorem exists_nonzero_domainIdentityMLE_of_helperSum_zero_of_fractionalSum_ne_zero
    (groups : Fin K → Finset (TermIdx M))
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


end Algebra

end Logup

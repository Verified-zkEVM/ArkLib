/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic.IndexAndSumcheck
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Algebra

/-!
# Binary Basefold protocol data

Statements, oracle statements and witnesses of the Binary Basefold rounds, the extraction
`extractMlp` of a multilinear polynomial from a first oracle close to the code
(`extractMlp_eq_some_iff_pairUniqueDecodingClose`), and the oracle snoc/take helpers.
-/

@[expose] public section

noncomputable section
namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

/-- A nontrivial algebra over a two-element field has characteristic two. -/
lemma charP_two_of_card_eq_two (K A : Type*) [Field K] [Fintype K]
    [Semiring A] [Nontrivial A] [Algebra K A] [hK : Fact (Fintype.card K = 2)] :
    CharP A 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_eq_prime hK.out
  exact charP_of_injective_algebraMap (algebraMap K A).injective 2

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
local instance instFactPrimeRingCharBasic [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section OracleReductionComponents
-- In this section, we use notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-!
## Core Protocol Structures

Basic structures and definitions used throughout the Binary Basefold protocol.
-/

-- `SumcheckBaseContext` and `Statement` are the structured sum-check's
-- (`ArkLib.ProofSystem.Sumcheck.Structured`), re-exported under `Binius.BinaryBasefold`.
export Sumcheck.Structured (SumcheckBaseContext Statement)

/-- Statement for the final sumcheck step - includes the final constant c -/
structure FinalSumcheckStatementOut extends
  Statement (L := L) (Context := SumcheckBaseContext L ℓ) (Fin.last ℓ) where
  finalConstant : L               -- c = f^(ℓ)(0, ..., 0)

/-- The committed codeword oracles available at state `i`, indexed by their frontier positions. -/
@[reducible]
def OracleStatement (ϑ : ℕ) [NeZero ϑ] (i : Fin (ℓ + 1)) :
    Fin (toOutCodewordsCount ℓ ϑ (i:=i)) → Type := fun j =>
  by
    let sDomainIdx := oraclePositionToDomainIndex ℓ ϑ j
    exact (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨sDomainIdx, by omega⟩ → L

/-- First oracle witness consistency: the witness polynomial t, when projected to level 0 and
    evaluated on the initial domain S^(0), must be close within unique decoding radius to f^(0) -/
def FirstOracleWitnessConsistent (t : MultilinearPoly L ℓ)
    (f₀ : sDomain 𝔽q β h_ℓ_add_R_rate 0 → L) : Prop :=
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => t.val.eval (bitsOfIndex ω))
  -- The constraint: P_0 evaluated on S^(0) is close within unique decoding radius to f^(0)
  PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)  (f := f₀)
    (g := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀))

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] hdiv in
/-- Oracle evaluation is invariant under equal oracle indices and transported equal points. -/
lemma OracleStatement.oracle_eval_congr
    -- Context: The oracle collection for a fixed round (usually Fin.last ℓ)
    {i : Fin (ℓ + 1)}
    (oStmtIn : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i j)
    -- 1. Outer Index Equality (j = j')
    {j j' : Fin (toOutCodewordsCount ℓ ϑ i)} (h_j : j = j')
    -- 2. Inner Point Equality (x = x')
    -- Note: x and x' have different types because they depend on j and j'
    {x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨oraclePositionToDomainIndex ℓ ϑ (i := i) j, by omega⟩}
    {x' : sDomain 𝔽q β h_ℓ_add_R_rate ⟨oraclePositionToDomainIndex ℓ ϑ (i := i) j', by omega⟩}
    (h_x : x = cast (by rw [h_j]) x') : oStmtIn j x = oStmtIn j' x' := by
  subst h_j; simp only [cast_eq] at h_x; subst h_x; rfl

/-- Transport the oracle frontier through a round without a commitment. -/
def mapOStmtOutRelayStep (i : Fin ℓ) (hNCR : ¬ IsCommitmentRound ℓ ϑ i)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j := fun j => by
  have h_oracle_size_eq: toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
  -- oracle index mapping
  exact oStmt ⟨j, by rw [h_oracle_size_eq]; omega⟩

/-- A multilinear source, its degree-two partial sum-check polynomial, and its folded codeword
at the current round. -/
structure Witness (i : Fin (ℓ + 1)) where
  t : L⦃≤ 1⦄[X Fin ℓ]  -- The original polynomial t
  H : L⦃≤ 2⦄[X Fin (ℓ - i)] -- Hᵢ
  f: (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L -- fᵢ

/-- The decoder enumerates its evaluation domain in the additive-NTT coordinate order. -/
def decoderDomainEquiv (i : Fin ℓ) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ ≃
      Fin (Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩)) := by
  rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega), hF₂.out]
  have h_equiv := sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
    (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)
  convert h_equiv

/-- Decode a codeword oracle and reconstruct its multilinear polynomial from novel-basis data. -/
def extractMlp (i : Fin ℓ) (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L) :
    Option (L⦃≤ 1⦄[X Fin (ℓ - i)]) := by
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩)
  set d := Code.distFromCode (u := f)
    (C := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let e: ℕ := d.toNat
  let k : ℕ := 2^(ℓ - i.val)  -- degree bound from code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by omega⟩ ≃ Fin domain_size := decoderDomainEquiv 𝔽q β i
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  let berlekamp_welch_result: Option L[X] := BerlekampWelch.decoder e k ωs f_vals
  match berlekamp_welch_result with
  | none => exact none  -- Decoder failed
  | some P =>
    -- 5. **post-decoding check** : Check if P's degree < 2^ℓ and `f` is UDR-Close to
      -- the encoding of `P`
    let isUDRClose := PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i,
      by omega⟩)
       (f := f) (g := polyToOracleFunc 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := ⟨i, by omega⟩) (P := P))
    if hP_valid: P.natDegree ≥ 2^(ℓ - i.val) ∨ (¬isUDRClose)  then
      exact none  -- Outside unique decoding radius
    else
      -- 6. Convert P(X) from monomial basis to novel polynomial basis
      -- P(X) = Σᵢ aᵢ Xᵢ (monomial) → P(X) = Σⱼ tⱼ X_{j}(X) (novel)
      -- We need the inverse of the change-of-basis matrix
      have h_deg_bound : P ∈ L[X]_(2^(ℓ - i.val)) := by
        rw [Polynomial.mem_degreeLT]
        by_cases hi: i = ℓ
        · simp only [hi, tsub_self, pow_zero, cast_one]
          by_cases hp_p_eq_0: P = 0
          · simp only [hp_p_eq_0, degree_zero]; omega
          · simp only [hi, tsub_self, pow_zero, ge_iff_le, not_or, not_le, lt_one_iff,
            not_not] at hP_valid
            have h_deg_p: P.degree = 0 := by omega
            simp only [h_deg_p]
            omega
        · by_cases hp_p_eq_0: P = 0
          · simp only [hp_p_eq_0];
            have h_i_lt_ℓ : i < ℓ := by omega
            simp only [degree_zero, cast_pow, cast_ofNat, gt_iff_lt]
            have h_deg_ne_bot : 2 ^ (ℓ - ↑i) ≠ ⊥ := by
              exact not_isBot_iff_ne_bot.mp fun a ↦ hP_valid (Or.inl (a P.natDegree))
            exact compareOfLessAndEq_eq_lt.mp rfl
          · have h := Polynomial.natDegree_lt_iff_degree_lt (p:=P) (n:=2 ^ (ℓ - ↑i))
              (hp:=by exact hp_p_eq_0)
            rw [←h]; omega
      -- Get monomial coefficients of P(X)
      let monomial_coeffs : Fin (2^(ℓ - i.val)) → L := fun i => P.coeff i.val
      -- Convert to novel polynomial basis coefficients using change of basis
      -- The changeOfBasisMatrix A has A[j,i] = coeff of X^i in novel basis vector X_j
      -- So we need A⁻¹ to convert monomial coeffs → novel coeffs
      -- Convert to the base novel basis used by the Boolean multilinear encoding.
      let t_coeffs : Fin (2^(ℓ - i.val)) → L :=
        AdditiveNTT.monomialToNovelCoeffs 𝔽q β (ℓ - i.val) (by omega) monomial_coeffs
      -- Interpret novel coeffs as Lagrange cosefficients on Boolean hypercube
      -- and reconstruct the multilinear polynomial using MLE
      let hypercube_evals : (Fin (ℓ - i.val) → Fin 2) → L := fun w =>
        -- Map Boolean hypercube point w to its linear index
        let w_index : Fin (2^(ℓ - i.val)) := Nat.binaryFinMapToNat
          (n:=ℓ - i.val) (m:=w) (h_binary:=by intro j; simp only [Nat.cast_id]; omega)
        t_coeffs w_index
      let t_multilinear_mv := MvPolynomial.MLE hypercube_evals
      exact some ⟨t_multilinear_mv, MLE_mem_restrictDegree hypercube_evals⟩

omit [DecidableEq 𝔽q] [NeZero ℓ] [NeZero 𝓡] in
/-- At the initial domain, the intermediate and base novel-coefficient maps agree. -/
private lemma monomialToINovelCoeffs_zero_eq_monomialToNovelCoeffs
    (monomial_coeffs : Fin (2 ^ ℓ) → L) :
    AdditiveNTT.monomialToINovelCoeffs 𝔽q β h_ℓ_add_R_rate
      (i := (0 : Fin r)) (h_i := by simp) monomial_coeffs =
      AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) monomial_coeffs := by
  have hA :
      AdditiveNTT.intermediateChangeOfBasisMatrix 𝔽q β h_ℓ_add_R_rate
        (i := (0 : Fin r)) (h_i := by simp) =
        AdditiveNTT.changeOfBasisMatrix 𝔽q β ℓ (by omega) := by
    ext j k
    change
      (intermediateNovelBasisX 𝔽q β h_ℓ_add_R_rate
        (i := (0 : Fin r)) (h_i := by simp) j).coeff k.val =
      (Xⱼ 𝔽q β ℓ (by omega) j).coeff k.val
    rw [AdditiveNTT.base_intermediateNovelBasisX
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (j := j)]
  simp only [AdditiveNTT.monomialToINovelCoeffs, AdditiveNTT.monomialToNovelCoeffs, hA]
  rw [Matrix.invOf_eq_nonsing_inv]
  rw [hA]
  rfl

omit [DecidableEq 𝔽q] [NeZero ℓ] [NeZero 𝓡] in
/-- Reconstructing from the novel coefficients of a bounded polynomial recovers it. -/
private lemma polynomialFromNovelCoeffs_eq_self_of_monomialToNovelCoeffs
    [NeZero 𝓡] (P : L[X]) (hP : P.degree < 2 ^ ℓ) :
    polynomialFromNovelCoeffs 𝔽q β ℓ (by omega)
      (AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) (fun k => P.coeff k.val)) = P := by
  have hget :
      getINovelCoeffs 𝔽q β h_ℓ_add_R_rate
        (i := (0 : Fin r)) (h_i := by simp) P =
        AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) (fun k => P.coeff k.val) := by
    simp [getINovelCoeffs, monomialToINovelCoeffs_zero_eq_monomialToNovelCoeffs
      (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)]
  let hbase := intermediate_poly_P_base (𝔽q := 𝔽q) (β := β)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (L := L) (ℓ := ℓ) (h_ℓ := by omega)
    (coeffs := getINovelCoeffs 𝔽q β h_ℓ_add_R_rate
      (i := (0 : Fin r)) (h_i := by simp) P)
  let hself := intermediateEvaluationPoly_from_inovel_coeffs_eq_self
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (L := L) (i := (0 : Fin r)) (h_i := by simp) (P := P) hP
  rw [hget] at hbase hself
  exact hbase.symm.trans hself

omit [NeZero ℓ] in
/-- Binary encoding followed by the inverse function equivalence recovers the bit vector. -/
private lemma binaryFinMapToNat_invFun_eq (ω : Fin (2 ^ ℓ)) :
    Nat.binaryFinMapToNat
      (n := ℓ)
      (m := fun i => ((finFunctionFinEquiv.invFun ω) i).val)
      (h_binary := by
        intro j
        exact Nat.le_of_lt_succ (finFunctionFinEquiv.invFun ω j).isLt) = ω := by
  apply Fin.eq_of_val_eq
  rw [Nat.eq_iff_eq_all_getBits]
  intro k
  rw [Nat.getBit_of_binaryFinMapToNat]
  split_ifs with hk
  · rw [Equiv.invFun_as_coe, finFunctionFinEquiv_symm_apply_val, Nat.getBit,
      Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  · have hk' : ℓ ≤ k := Nat.le_of_not_gt hk
    have hω_lt : (ω : ℕ) < 2 ^ k := by
      calc
        (ω : ℕ) < 2 ^ ℓ := ω.isLt
        _ ≤ 2 ^ k := by
          exact Nat.pow_le_pow_right (by omega) hk'
    rw [Nat.getBit_eq_testBit, Nat.testBit_eq_false_of_lt hω_lt]
    simp

omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- The multilinear extension of novel coefficients evaluates to each indexed coefficient. -/
private lemma extracted_mle_eval_bits [NeZero 𝓡] (P : L[X]) (ω : Fin (2 ^ ℓ)) :
    let monomial_coeffs : Fin (2 ^ ℓ) → L := fun k => P.coeff k.val
    let t_coeffs := AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) monomial_coeffs
    let hypercube_evals : (Fin ℓ → Fin 2) → L := fun w =>
      let w_index : Fin (2 ^ ℓ) := Nat.binaryFinMapToNat
        (n := ℓ) (m := fun i => (w i).val)
        (h_binary := by
          intro j
          exact Nat.le_of_lt_succ (w j).isLt)
      t_coeffs w_index
    MvPolynomial.eval (bitsOfIndex (L := L) ω) (MvPolynomial.MLE hypercube_evals) = t_coeffs ω := by
  let t_coeffs : Fin (2 ^ ℓ) → L :=
    AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) (fun k => P.coeff k.val)
  dsimp only
  rw [← coe_fin_pow_two_eq_bitsOfIndex (L := L) (k := ω)]
  rw [MvPolynomial.MLE_eval_zeroOne]
  have h_index := congrArg (fun x => t_coeffs x) (binaryFinMapToNat_invFun_eq (ℓ := ℓ) ω)
  exact h_index

omit [DecidableEq 𝔽q] [NeZero ℓ] [NeZero 𝓡] in
/-- Encoding the reconstructed multilinear extension recovers the bounded polynomial. -/
private lemma extracted_mle_polynomial_eq
    [NeZero 𝓡] (P : L[X]) (hP : P.degree < 2 ^ ℓ) :
    polynomialFromNovelCoeffs 𝔽q β ℓ (by omega)
      (fun ω =>
        let monomial_coeffs : Fin (2 ^ ℓ) → L := fun k => P.coeff k.val
        let t_coeffs := AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) monomial_coeffs
        let hypercube_evals : (Fin ℓ → Fin 2) → L := fun w =>
          let w_index : Fin (2 ^ ℓ) := Nat.binaryFinMapToNat
            (n := ℓ) (m := fun i => (w i).val)
            (h_binary := by
              intro j
              exact Nat.le_of_lt_succ (w j).isLt)
          t_coeffs w_index
        MvPolynomial.eval (bitsOfIndex (L := L) ω) (MvPolynomial.MLE hypercube_evals)) = P := by
  let t_coeffs : Fin (2 ^ ℓ) → L :=
    AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) (fun k => P.coeff k.val)
  have h_eval :
      (fun ω =>
        let monomial_coeffs : Fin (2 ^ ℓ) → L := fun k => P.coeff k.val
        let t_coeffs := AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega) monomial_coeffs
        let hypercube_evals : (Fin ℓ → Fin 2) → L := fun w =>
          let w_index : Fin (2 ^ ℓ) := Nat.binaryFinMapToNat
            (n := ℓ) (m := fun i => (w i).val)
            (h_binary := by
              intro j
              exact Nat.le_of_lt_succ (w j).isLt)
          t_coeffs w_index
        MvPolynomial.eval (bitsOfIndex (L := L) ω)
          (MvPolynomial.MLE hypercube_evals)) = t_coeffs := by
    funext ω
    exact extracted_mle_eval_bits (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (P := P) ω
  rw [h_eval]
  exact polynomialFromNovelCoeffs_eq_self_of_monomialToNovelCoeffs
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (P := P) hP

omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- The encoded polynomial coefficients are the converted novel coefficients. -/
private lemma coeff_polynomialFromNovelCoeffsF₂_eq_novelToMonomialCoeffs
    (coeffs : Fin (2 ^ ℓ) → L) :
    (fun k =>
      (↑(polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) coeffs) : L[X]).coeff k.val) =
      AdditiveNTT.novelToMonomialCoeffs 𝔽q β ℓ (by omega) coeffs := by
  funext k
  change
    (AdditiveNTT.polynomialFromNovelCoeffs 𝔽q β ℓ (by omega) coeffs).coeff k.val =
      AdditiveNTT.novelToMonomialCoeffs 𝔽q β ℓ (by omega) coeffs k
  unfold AdditiveNTT.polynomialFromNovelCoeffs AdditiveNTT.novelToMonomialCoeffs
  simp only [finsetSum_coeff, Polynomial.coeff_C_mul]
  have h_matrix_def :
      ∀ j : Fin (2 ^ ℓ),
        (Xⱼ 𝔽q β ℓ (by omega) j).coeff k.val =
          (AdditiveNTT.changeOfBasisMatrix 𝔽q β ℓ (by omega)) j k := by
    intro j
    dsimp only [AdditiveNTT.changeOfBasisMatrix, AdditiveNTT.toCoeffsVec,
      AdditiveNTT.basisVectors, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [h_matrix_def]
  dsimp only [Matrix.vecMul, dotProduct]

omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- Converting the encoded polynomial coefficients recovers its novel coefficients. -/
private lemma monomialToNovelCoeffs_polynomialFromNovelCoeffsF₂
    (coeffs : Fin (2 ^ ℓ) → L) :
    AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega)
      (fun k =>
        (↑(polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) coeffs) : L[X]).coeff k.val) = coeffs := by
  rw [coeff_polynomialFromNovelCoeffsF₂_eq_novelToMonomialCoeffs
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (coeffs := coeffs)]
  exact AdditiveNTT.novelToMonomial_monomialToNovel_inverse 𝔽q β ℓ (by omega) coeffs

/-- For index 0, `extractMlp 0 f = some tpoly` iff `f` is pair-UDR-close to the oracle function
of the multilinear polynomial `tpoly` (i.e. the polynomial-as-oracle from novel coeffs of tpoly).
Forward: decoder succeeds only when within UDR. Backward: within UDR the decoded codeword
is `polyToOracleFunc (polynomialFromNovelCoeffsF₂ tpoly)`. -/
lemma extractMlp_eq_some_iff_pairUniqueDecodingClose
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, by omega⟩ → L)
    (tpoly : MultilinearPoly L ℓ) :
    (extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f = some tpoly) ↔
    PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0)
      (f := f)
      (g := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0)
        (P := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
          (fun ω => tpoly.val.eval (bitsOfIndex ω)))) := by
  classical
  change (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r) → L) at f
  constructor
  · intro h_extract
    unfold extractMlp at h_extract
    simp only [Fin.coe_ofNat_eq_mod, zero_mod, Nat.sub_zero, ge_iff_le] at h_extract
    split at h_extract
    · cases h_extract
    · rename_i berlekamp_welch_result P h_decoder
      by_cases h_invalid : P.natDegree ≥ 2 ^ ℓ ∨ ¬ PairUniqueDecodingClose 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin r))  (f := f)
          (g := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (domainIdx := 0) (P := P))
      · simp only [ge_iff_le, Fin.mk_zero', h_invalid, ↓reduceDIte, reduceCtorEq] at h_extract
      · simp only [ge_iff_le, Fin.mk_zero', h_invalid, ↓reduceDIte, Nat.cast_id,
          Option.some.injEq] at h_extract
        have h_natdeg_lt : P.natDegree < 2 ^ ℓ := by
          have h_not_ge : ¬ P.natDegree ≥ 2 ^ ℓ := by
            intro h_ge
            exact h_invalid (Or.inl h_ge)
          exact Nat.lt_of_not_ge h_not_ge
        have h_closeP : PairUniqueDecodingClose 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r))  (f := f)
            (g := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (domainIdx := 0) (P := P)) := by
          by_contra h_not_close
          exact h_invalid (Or.inr h_not_close)
        have h_deg_lt : P.degree < 2 ^ ℓ := by
          by_cases hP_zero : P = 0
          · simp only [hP_zero, degree_zero]
            exact compareOfLessAndEq_eq_lt.mp rfl
          · have h_natDegree_lt_iff := Polynomial.natDegree_lt_iff_degree_lt
                (p := P) (n := 2 ^ ℓ) (hp := hP_zero)
            exact h_natDegree_lt_iff.mp h_natdeg_lt
        have htpoly := h_extract
        have h_mle := congrArg Subtype.val htpoly
        have h_poly :
            (↑(polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
              (fun ω =>
                MvPolynomial.eval (bitsOfIndex ω) tpoly.val)) : L[X]) = P := by
          rw [← h_mle]
          change polynomialFromNovelCoeffs 𝔽q β ℓ (by omega) _ = P
          exact extracted_mle_polynomial_eq (𝔽q := 𝔽q) (β := β)
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (P := P) h_deg_lt
        rw [h_poly]
        exact h_closeP
  · intro h_close
    unfold extractMlp
    simp only [Fin.coe_ofNat_eq_mod, zero_mod, Nat.sub_zero, ge_iff_le]
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, by omega⟩ ≃ Fin domain_size :=
      decoderDomainEquiv 𝔽q β 0
    let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
    let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
    let P₀ : L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
      (fun ω => tpoly.val.eval (bitsOfIndex ω))
    let g₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := (0 : Fin r)) (P := P₀)
    let C₀ := (↑(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) :
      Set ((sDomain 𝔽q β h_ℓ_add_R_rate) (0 : Fin r) → L))
    have h_domain_size : domain_size = 2 ^ (ℓ + 𝓡) := by
      dsimp [domain_size]
      change Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate (0 : Fin r)) = 2 ^ (ℓ + 𝓡)
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
        (i := (0 : Fin r))
        (h_i := lt_rounds_add_rate_of_le_rounds (𝓡 := 𝓡) (x := 0) (Nat.zero_le ℓ)), hF₂.out]
      simp
    have h_g₀_mem : g₀ ∈ C₀ := by
      dsimp [g₀, C₀]
      exact (polynomialCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r))  P₀).property
    have : Nonempty C₀ := ⟨⟨g₀, h_g₀_mem⟩⟩
    have : NeZero ‖C₀‖₀ := by
      refine ⟨?_⟩
      have h_code_distance : ‖C₀‖₀ = 2 ^ (ℓ + 𝓡) - 2 ^ ℓ + 1 := by
        dsimp [C₀]
        exact codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ)
      rw [h_code_distance]
      omega
    have h_close_udr :
        Δ₀(f, g₀) ≤ Code.uniqueDecodingRadius (C := C₀) := by
      dsimp [g₀, C₀] at h_close ⊢
      rw [Code.UDRClose_iff_two_mul_proximity_lt_d_UDR (C := C₀)]
      exact h_close
    have h_pick_eq :
        (Code.pickClosestCodeword_of_Nonempty_Code C₀ f : C₀) = ⟨g₀, h_g₀_mem⟩ := by
      exact Code.pickClosestCodeword_eq_of_le_uniqueDecodingRadius
        (C := C₀) (u := f) h_g₀_mem h_close_udr
    have h_dist_eq :
        Δ₀(f, C₀) = (Δ₀(f, g₀) : ENat) := by
      rw [Code.distFromPickClosestCodeword_of_Nonempty_Code (C := C₀) (u := f)]
      rw [h_pick_eq]
    have h_dist_eq_nat : (Δ₀(f, C₀)).toNat = Δ₀(f, g₀) := by
      rw [h_dist_eq]
      simp
    have h_P₀_natDegree_lt : (↑P₀ : L[X]).natDegree < 2 ^ ℓ := by
      by_cases hP₀_zero : (↑P₀ : L[X]) = 0
      · rw [hP₀_zero, Polynomial.natDegree_zero]
        exact pow_pos (by decide : 0 < 2) _
      · have hP₀_deg_lt : (↑P₀ : L[X]).degree < 2 ^ ℓ := by
          have hP₀_mem : (↑P₀ : L[X]) ∈ L[X]_(2 ^ ℓ) := P₀.property
          rw [Polynomial.mem_degreeLT] at hP₀_mem
          exact hP₀_mem
        exact (Polynomial.natDegree_lt_iff_degree_lt (p := (↑P₀ : L[X]))
          (n := 2 ^ ℓ) (hp := hP₀_zero)).2 hP₀_deg_lt
    have h_decoder_succeeds :
        BerlekampWelch.decoder (Δ₀(f, C₀)).toNat (2 ^ ℓ) ωs f_vals = some (↑P₀ : L[X]) := by
      apply BerlekampWelch.decoder_eq_some
      · have h_le :
            2 * (Δ₀(f, C₀)).toNat ≤ domain_size - 2 ^ ℓ := by
          rw [h_dist_eq_nat]
          have h_close' := h_close
          dsimp [PairUniqueDecodingClose, g₀] at h_close'
          rw [codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r)) (h_i := Nat.zero_le ℓ)] at h_close'
          rw [h_domain_size]
          exact Nat.le_of_lt_succ h_close'
        exact Nat.lt_succ_of_le h_le
      · rw [h_domain_size]
        exact Nat.pow_le_pow_right (by omega) (Nat.le_add_right ℓ 𝓡)
      · exact Function.Injective.comp Subtype.val_injective (Equiv.injective domain_to_fin.symm)
      · exact h_P₀_natDegree_lt
      · have h_functions_eq :
            (fun a => Polynomial.eval a (↑P₀ : L[X])) ∘ ωs = g₀ ∘ domain_to_fin.symm := by
          ext j
          simp only [Function.comp_apply, ωs, g₀]
          rfl
        rw [h_functions_eq]
        calc
          hammingDist f_vals (g₀ ∘ domain_to_fin.symm)
              ≤ hammingDist f g₀ := by
                apply hammingDist_comp_le_of_injective f g₀ domain_to_fin.symm
                exact Equiv.injective domain_to_fin.symm
          _ = (Δ₀(f, C₀)).toNat := by
                exact h_dist_eq_nat.symm
    have h_not_invalid :
        ¬((↑P₀ : L[X]).natDegree ≥ 2 ^ ℓ ∨
          ¬PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := (0 : Fin r))  (f := f) (g := g₀)) := by
      intro h_invalid
      rcases h_invalid with h_deg_ge | h_not_close
      · exact (not_le_of_gt h_P₀_natDegree_lt) h_deg_ge
      · exact h_not_close h_close
    let decodePoly : L[X] → MultilinearPoly L ℓ := fun P =>
      ⟨MvPolynomial.MLE (fun w =>
          AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega)
            (fun i => P.coeff i.val)
            (Nat.binaryFinMapToNat
              (n := ℓ) (m := fun i => (w i).val)
              (h_binary := by
                intro j
                exact Nat.le_of_lt_succ (w j).isLt))),
        MLE_mem_restrictDegree _⟩
    have h_not_invalid' := h_not_invalid
    dsimp [g₀] at h_not_invalid'
    have h_target :
        ((match BerlekampWelch.decoder (Δ₀(f, C₀)).toNat (2 ^ ℓ) ωs f_vals with
        | none => none
        | some P =>
            if h : P.natDegree ≥ 2 ^ ℓ ∨
                ¬PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                  (i := (0 : Fin r))  (f := f)
                  (g := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
                    (domainIdx := (0 : Fin r)) (P := P))
            then none
            else
              some (decodePoly P)) = some tpoly) := by
      rw [h_decoder_succeeds]
      simp only [h_not_invalid']
      split_ifs with h_false
      · contradiction
      apply congrArg Option.some
      dsimp [decodePoly]
      apply (MvPolynomial.MLEEquivFin (R := L) (n := ℓ)).injective
      funext ω
      dsimp [MvPolynomial.MLEEquivFin, MvPolynomial.MLEEquiv]
      have hω : finFunctionFinEquiv (finFunctionFinEquiv.symm ω) = ω := by simp
      rw [← hω]
      rw [Equiv.piCongr_apply_apply (a := finFunctionFinEquiv.symm ω)]
      rw [Equiv.piCongr_apply_apply (a := finFunctionFinEquiv.symm ω)]
      simp only [Equiv.refl_apply, MvPolynomial.MLE_eval_zeroOne]
      rw [monomialToNovelCoeffs_polynomialFromNovelCoeffsF₂
        (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (coeffs := fun ω => tpoly.val.eval (bitsOfIndex ω))]
      have h_index :
          Nat.binaryFinMapToNat
            (n := ℓ)
            (m := fun i => ((finFunctionFinEquiv.symm ω i : Fin 2) : ℕ))
            (h_binary := by
              intro j
              exact Nat.le_of_lt_succ (finFunctionFinEquiv.symm ω j).isLt) = ω := by
        exact binaryFinMapToNat_invFun_eq (ℓ := ℓ) ω
      rw [h_index]
      have h_bits :
          (fun i => ↑↑(finFunctionFinEquiv.symm ω i)) = bitsOfIndex (L := L) ω := by
        exact coe_fin_pow_two_eq_bitsOfIndex (L := L) (k := ω)
      rw [h_bits]
    exact h_target

/-- Extractor success identifies the unique decoded word with the polynomial encoding. -/
lemma uniqueDecodingCodeword_eq_of_extractMlp_eq_some
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (t : MultilinearPoly L ℓ)
    (h_extract : extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f = some t)
    (h_close : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f) :
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 (by simp) f h_close =
      polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0)
        (polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
          (fun ω => t.val.eval (bitsOfIndex ω))) := by
  let P := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
    (fun ω => t.val.eval (bitsOfIndex ω))
  let C : Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r)) :=
    code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
  let : NeZero ‖C‖₀ := codeDistance_neZero 𝔽q β 0
  have h_pair := (extractMlp_eq_some_iff_pairUniqueDecodingClose 𝔽q β f t).mp h_extract
  have h_dist : Δ₀(f, polyToOracleFunc 𝔽q β (domainIdx := 0) P) ≤
      Code.uniqueDecodingRadius C :=
    (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR C).2 h_pair
  exact ((uniqueDecodingCodeword_spec 𝔽q β 0 (by simp) f h_close).2.2 _
    (polynomialCodeword 𝔽q β 0 P).property h_dist).symm

/-- Fiberwise closeness at the initial domain implies successful multilinear extraction. -/
lemma extractMlp_zero_isSome_of_fiberwiseClose
    {destIdx : Fin r} {steps : ℕ}
    (h_destIdx : destIdx = steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f₀ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r))
    (h_fw_close_zero : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) steps (by simpa using h_destIdx) h_destIdx_le f₀) :
    ∃ tpoly : MultilinearPoly L ℓ,
      extractMlp 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 f₀ = some tpoly := by
  have hzero : (0 : Fin r).val = 0 := by simp
  classical
  have h_udr_f₀ :
      UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r))  f₀ := by
    exact uniqueDecodingClose_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r))
      (steps := steps) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (f := f₀) h_fw_close_zero
  let g₀ := uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := (0 : Fin r)) (h_i := by omega) (f := f₀) h_udr_f₀
  have h_g₀_mem :
      g₀ ∈ (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
        Set ((sDomain 𝔽q β h_ℓ_add_R_rate) 0 → L)) := by
    exact uniqueDecodingCodeword_mem_code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := (0 : Fin r)) (h_i := by omega) (f := f₀) h_udr_f₀
  let g₀_sub : code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) := ⟨g₀, h_g₀_mem⟩
  let P₀ := codewordPolynomial 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) g₀_sub
  let t_evals : (Fin ℓ → Fin 2) → L := fun w =>
    AdditiveNTT.monomialToNovelCoeffs 𝔽q β ℓ (by omega)
      (fun k => (↑P₀ : L[X]).coeff k.val)
      (Nat.binaryFinMapToNat
        (n := ℓ) (m := fun j => (w j).val)
        (h_binary := by
          intro j
          exact Nat.le_of_lt_succ (w j).isLt))
  let tpoly : MultilinearPoly L ℓ := ⟨MvPolynomial.MLE t_evals, MLE_mem_restrictDegree t_evals⟩
  have h_pair_close :
      PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := (0 : Fin r))  (f := f₀)
        (g := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (domainIdx := 0) (P := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega)
            (fun ω => tpoly.val.eval (bitsOfIndex ω)))) := by
    have h_udr_g₀ :
        Δ₀(f₀, g₀) ≤ Code.uniqueDecodingRadius
          (C := (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
            Set ((sDomain 𝔽q β h_ℓ_add_R_rate) 0 → L))) := by
      exact dist_to_uniqueDecodingCodeword_le_uniqueDecodingRadius 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := (0 : Fin r))
        (h_i := by omega) (f := f₀) h_udr_f₀
    have :
        NeZero ‖(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
          Set ((sDomain 𝔽q β h_ℓ_add_R_rate) 0 → L))‖₀ := by
      refine ⟨?_⟩
      have h_code_distance :
          ‖(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
            Set ((sDomain 𝔽q β h_ℓ_add_R_rate) 0 → L))‖₀ =
            2 ^ (ℓ + 𝓡) - 2 ^ ℓ + 1 := by
        exact codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin r)) (h_i := by omega)
      rw [h_code_distance]
      omega
    have h_pair_close_g₀ :
        PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := (0 : Fin r))  (f := f₀) (g := g₀) := by
      dsimp [PairUniqueDecodingClose, g₀] at ⊢
      rw [Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
        (C := (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (0 : Fin r) :
          Set ((sDomain 𝔽q β h_ℓ_add_R_rate) 0 → L)))] at h_udr_g₀
      exact h_udr_g₀
    have h_P₀_deg_lt : (↑P₀ : L[X]).degree < 2 ^ ℓ := by
      have hP₀_mem : (↑P₀ : L[X]) ∈ L[X]_(2 ^ ℓ) := P₀.property
      rw [Polynomial.mem_degreeLT] at hP₀_mem
      exact hP₀_mem
    have h_g₀_eq :
        g₀ = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (domainIdx := (0 : Fin r)) (P := P₀) := by
      exact codewordPolynomial_spec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (0 : Fin r) g₀_sub
    dsimp [tpoly, t_evals, polynomialFromNovelCoeffsF₂]
    rw [extracted_mle_polynomial_eq (𝔽q := 𝔽q) (β := β)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (P := (↑P₀ : L[X])) h_P₀_deg_lt]
    rw [← h_g₀_eq]
    exact h_pair_close_g₀
  refine ⟨tpoly, ?_⟩
  exact (extractMlp_eq_some_iff_pairUniqueDecodingClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (f := f₀) (tpoly := tpoly)).2 h_pair_close

/-- The zero polynomial, residual polynomial and word form a witness at the last state. -/
def dummyLastWitness :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) := {
  t := ⟨0, by apply zero_mem⟩,
  H := ⟨0, by apply zero_mem⟩,
  f := fun _ => 0
}

section SnocOracleHelpers
omit [NeZero ℓ] [NeZero ϑ] in
/-- Outside a commitment round, the oracle count does not increase,
    so an index `j` cannot exist in the range `[old_count, new_count)`. -/
lemma false_of_newOracleIndex_of_not_isCommitmentRound {i : Fin ℓ}
    {j : Fin (toOutCodewordsCount ℓ ϑ i.succ)}
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc)
    (h_not_commit : ¬ IsCommitmentRound ℓ ϑ i) : False := by
  -- The count relation implies new_count = old_count
  have h_counts_eq : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc := by
    rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [h_not_commit, ↓reduceIte]
  -- But j is bounded by new_count
  have h_j_lt_new := j.isLt
  conv_rhs at h_j_lt_new => rw [h_counts_eq]
  -- Contradiction with hj
  exact hj h_j_lt_new

omit [NeZero r] [NeZero 𝓡] in
/-- At a commitment round, the index `j` (which is ≥ old_count)
    must be exactly equal to `old_count`, and consequently its domain index corresponds
    to `destIdx` (which is `i + 1`). -/
lemma destIdx_eq_oraclePositionToDomainIndex_of_newOracle {i : Fin ℓ} {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc)
    (h_commit : IsCommitmentRound ℓ ϑ i) :
    destIdx = ⟨(oraclePositionToDomainIndex ℓ ϑ j).val,
               by have := oraclePositionToDomainIndex ℓ ϑ j; omega⟩ := by
  -- 1. Prove counts relation: new = old + 1
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ =
      toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [h_commit, ↓reduceIte]
  -- 2. Prove j must be exactly old_count
  have h_j_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
    have h_lt := j.isLt
    conv_rhs at h_lt => rw [h_count_succ]
    -- j < old + 1 AND NOT j < old  =>  j = old
    omega
  -- 3. Calculate the domain index value for j
  -- We need to prove: destIdx.val = j * ϑ
  apply Fin.eq_of_val_eq
  simp only [h_destIdx]
  -- We know j * ϑ = i + 1 from the structure of commitment rounds
  rw [h_j_eq]
  rw [toOutCodewordsCount_castSucc_mul_eq_succ_of_dvd ℓ ϑ i h_commit.1]

/-- snocOracle adds the latest oracle function to the end of an oStmtIn -/
def snocOracle {i : Fin ℓ} {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.succ),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i.succ j := fun j =>
  if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
      -- Case 1: Old oracle (index < old count)
      oStmtIn ⟨j.val, hj⟩
    else
      if hi : IsCommitmentRound ℓ ϑ i then
        -- Case 2: New oracle (Commitment round, index == old count)
        -- Derive the equality between the function's expected domain and the actual domain
        let h_eq := destIdx_eq_oraclePositionToDomainIndex_of_newOracle (h_ℓ_add_R_rate :=
          h_ℓ_add_R_rate)
          (ℓ := ℓ) (ϑ := ϑ) h_destIdx j hj hi
        fun x => newOracleFn (cast (by rw [h_eq]) x)
      else
        -- Case 3: Impossible (Not commitment round, but index increased)
        (false_of_newOracleIndex_of_not_isCommitmentRound hj hi).elim

/-- Restrict an updated oracle frontier to the preceding state. -/
def takeSnocOracle (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) → -- We specify range type so Lean won't be stuck
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j :=
  fun j => snocOracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx
      oStmtIn newOracleFn ⟨j, by
        have h : (toOutCodewordsCount ℓ ϑ i.castSucc) ≤ toOutCodewordsCount ℓ ϑ i.succ := by
          exact toOutCodewordsCount_castSucc_le_succ ℓ ϑ i
        omega
      ⟩

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- Restricting an extended oracle frontier recovers the original frontier. -/
lemma takeSnocOracle_eq_oStmtIn (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    (takeSnocOracle 𝔽q β i h_destIdx oStmtIn newOracleFn) = oStmtIn := by
  unfold takeSnocOracle snocOracle
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

end SnocOracleHelpers

/-- Extract the first oracle f^(0) from oracle statements -/
def getFirstOracle {oracleFrontierIdx : Fin (ℓ + 1)}
    (oStmt : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ oracleFrontierIdx j)) :
    sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩→ L :=
  let rawf₀ := oStmt ⟨0, by
    let := instNeZeroNatToOutCodewordsCount ℓ ϑ oracleFrontierIdx
    exact pos_of_neZero (toOutCodewordsCount ℓ ϑ oracleFrontierIdx)
  ⟩
  fun y => rawf₀ (cast (by simp only [Fin.mk_zero', zero_mul]) y)

/-- Read the last committed codeword at its transported domain index. -/
def getLastOracle {oracleFrontierIdx : Fin (ℓ + 1)} {destIdx : Fin r}
    (h_destIdx : destIdx.val = getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx)
    (oStmt : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      (i := oracleFrontierIdx) j)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  let res := oStmt ⟨getLastOraclePositionIndex ℓ ϑ oracleFrontierIdx, by omega⟩
  have h_lt : getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx < r := by omega
  have h_eq : destIdx = ⟨getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx, h_lt⟩ :=
    Fin.eq_of_val_eq (by omega)
  fun y => res (cast (by rw [h_eq]) y)

end OracleReductionComponents

end Binius.BinaryBasefold

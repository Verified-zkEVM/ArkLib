/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-!
# Binding of the initial Binary Basefold oracle

The initial oracle is related to a multilinear witness by strict unique-radius proximity to its
novel-basis Reed–Solomon encoding. This module proves that this existing relation determines the
witness uniquely, and that the honest encoding satisfies it. These facts concern the commitment
relation; they do not assert soundness of Binary Basefold's opening protocol.
-/

noncomputable section

namespace Binius.BinaryBasefold

open AdditiveNTT Polynomial MvPolynomial Module Sumcheck.Structured

/-- The LSB-first Boolean evaluation table determines a multilinear polynomial. -/
theorem witnessNovelCoeffs_injective {L : Type} [Field L] {ℓ : ℕ} :
    Function.Injective (witnessNovelCoeffs (L := L) (ℓ := ℓ)) := by
  intro t u h
  apply Subtype.ext
  apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq t.val u.val
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp t.property)
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp u.property)
  intro x
  let ω := Nat.binaryFinMapToNat (fun j => (x j).val) (fun j => by omega)
  have hpoint : (fun j : Fin ℓ => (Nat.getBit j.val ω.val : L)) =
      (x : Fin ℓ → L) := by
    funext j
    simp only [ω, Nat.getBit_of_binaryFinMapToNat, j.isLt, dite_true]
  simpa only [witnessNovelCoeffs, hpoint] using congrFun h ω

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K]
variable [hF₂ : Fact (Fintype.card K = 2)] [Algebra K L]
variable (β : Fin r → L) [Fact (LinearIndependent K β)]

/-- Synthesis in the actual novel polynomial basis is injective on coefficient vectors. -/
theorem polynomialFromNovelCoeffsF₂_injective (ℓ : ℕ) (hℓ : ℓ ≤ r) :
    Function.Injective (polynomialFromNovelCoeffsF₂ K β ℓ hℓ) := by
  have hsynth (a : Fin (2 ^ ℓ) → L) :
      polynomialFromNovelCoeffsF₂ K β ℓ hℓ a =
        (novelPolynomialBasis K β ℓ hℓ).equivFun.symm a := by
    apply Subtype.ext
    rw [Basis.equivFun_symm_apply]
    simp only [polynomialFromNovelCoeffsF₂, polynomialFromNovelCoeffs,
      novelPolynomialBasis_is_basisVectors, Submodule.coe_sum, Submodule.coe_smul,
      basisVectors, Polynomial.smul_eq_C_mul]
  intro a b h
  rw [hsynth a, hsynth b] at h
  exact (novelPolynomialBasis K β ℓ hℓ).equivFun.symm.injective h

variable [Fact (Nat.Prime (ringChar K))]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- The initial Binary Basefold domain has the advertised binary size. -/
theorem initialDomain_card :
    Fintype.card (sDomain K β h_ℓ_add_R_rate 0) = 2 ^ (ℓ + 𝓡) := by
  rw [sDomain_card K β h_ℓ_add_R_rate 0 (by simpa using
    (Nat.add_pos_left (Nat.pos_of_ne_zero (NeZero.ne ℓ)) 𝓡)), hF₂.out]
  simp

/-- The initial domain contains enough points to determine the encoded polynomial. -/
theorem initialDomain_degree_le_card :
    2 ^ ℓ ≤ Fintype.card (sDomain K β h_ℓ_add_R_rate 0) := by
  rw [initialDomain_card K β]
  exact Nat.pow_le_pow_right (by omega) (Nat.le_add_right ℓ 𝓡)

/-- `BBF_CodeDistance` is the actual minimum distance at the initial oracle. -/
theorem initialCode_minDist :
    Code.minDist (BBF_Code K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0).carrier =
      BBF_CodeDistance ℓ 𝓡 0 := by
  change Code.minDist (ReedSolomon.code
    (⟨Subtype.val, Subtype.val_injective⟩ : sDomain K β h_ℓ_add_R_rate 0 ↪ L)
    (2 ^ ℓ)).carrier = BBF_CodeDistance ℓ 𝓡 0
  have hd := ReedSolomon.minDist_of_le
    (α := (⟨Subtype.val, Subtype.val_injective⟩ : sDomain K β h_ℓ_add_R_rate 0 ↪ L))
    (initialDomain_degree_le_card K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  simpa [initialDomain_card K β, BBF_CodeDistance] using hd

/-- Evaluate a polynomial of the initial degree bound on the actual initial domain. -/
def initialPolynomialEncoding (p : L⦃< 2 ^ ℓ⦄[X]) :
    sDomain K β h_ℓ_add_R_rate 0 → L := fun x => p.val.eval x.val

/-- Evaluation on the initial domain is injective at the advertised degree bound. -/
theorem initialPolynomialEncoding_injective :
    Function.Injective (initialPolynomialEncoding K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  intro p q h
  have hcard : (2 ^ ℓ : ℕ) ≤ Finset.univ.card (α := sDomain K β h_ℓ_add_R_rate 0) := by
    simpa using initialDomain_degree_le_card K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (v := fun x => x.val)
    (s := Finset.univ (α := sDomain K β h_ℓ_add_R_rate 0))
  · exact Subtype.val_injective.injOn
  · exact (Polynomial.mem_degreeLT.mp p.property).trans_le (by exact_mod_cast hcard)
  · exact (Polynomial.mem_degreeLT.mp q.property).trans_le (by exact_mod_cast hcard)
  · intro x _
    exact congrFun h x

/-- The honest first oracle is the novel-basis encoding of the Boolean table. -/
def firstOracleEncoding (t : MultilinearPoly L ℓ) : sDomain K β h_ℓ_add_R_rate 0 → L :=
  initialPolynomialEncoding K β (polynomialFromNovelCoeffsF₂ K β ℓ (by omega)
    (witnessNovelCoeffs t))

omit [NeZero ℓ] in
/-- An honest first oracle belongs to the actual initial Reed–Solomon code. -/
theorem firstOracleEncoding_mem_code (t : MultilinearPoly L ℓ) :
    firstOracleEncoding K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t ∈
      BBF_Code K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 := by
  exact ⟨(polynomialFromNovelCoeffsF₂ K β ℓ (by omega) (witnessNovelCoeffs t)).val,
    (polynomialFromNovelCoeffsF₂ K β ℓ (by omega) (witnessNovelCoeffs t)).property, rfl⟩

/-- The honest first-oracle encoder is injective. -/
theorem firstOracleEncoding_injective :
    Function.Injective (firstOracleEncoding K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  intro t u h
  apply witnessNovelCoeffs_injective
  apply polynomialFromNovelCoeffsF₂_injective K β ℓ (by omega)
  exact initialPolynomialEncoding_injective K β h

/-- The production proximity relation fixes the multilinear witness before any challenge. -/
theorem firstOracleWitnessConsistencyProp_functional
    (f₀ : sDomain K β h_ℓ_add_R_rate 0 → L) (t u : MultilinearPoly L ℓ)
    (ht : firstOracleWitnessConsistencyProp K β t f₀)
    (hu : firstOracleWitnessConsistencyProp K β u f₀) : t = u := by
  apply firstOracleEncoding_injective K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  apply Code.eq_of_lt_dist (firstOracleEncoding_mem_code K β t)
    (firstOracleEncoding_mem_code K β u)
  change hammingDist (firstOracleEncoding K β t) (firstOracleEncoding K β u) <
    Code.dist (BBF_Code K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0).carrier
  have hd := initialCode_minDist K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  rw [Code.dist_eq_minDist] at ⊢
  change hammingDist (firstOracleEncoding K β t) (firstOracleEncoding K β u) <
    Code.minDist (BBF_Code K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0).carrier
  rw [hd]
  change 2 * hammingDist (firstOracleEncoding K β t) f₀ < _ at ht
  change 2 * hammingDist (firstOracleEncoding K β u) f₀ < _ at hu
  have htri := hammingDist_triangle (firstOracleEncoding K β t) f₀
    (firstOracleEncoding K β u)
  rw [hammingDist_comm f₀] at htri
  simp only [BBF_CodeDistance, Fin.val_zero, Nat.sub_zero] at ht hu ⊢
  omega

omit [NeZero ℓ] in
/-- Every multilinear witness has an honest oracle satisfying the production relation. -/
theorem firstOracleWitnessConsistencyProp_honest (t : MultilinearPoly L ℓ) :
    firstOracleWitnessConsistencyProp K β t
      (firstOracleEncoding K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t) := by
  change 2 * hammingDist (firstOracleEncoding K β t) (firstOracleEncoding K β t) < _
  rw [hammingDist_self]
  simp [BBF_CodeDistance]

variable (ϑ : ℕ) [NeZero ϑ] [Fact (ϑ ∣ ℓ)]

/-- The actual initial oracle family carrying the honest first codeword. -/
def honestInitialOracleStatement (t : MultilinearPoly L ℓ) :
    ∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j := by
  let j₀ : Fin (toOutCodewordsCount ℓ ϑ 0) := ⟨0, by
    rw [toOutCodewordsCountOf0]
    omega⟩
  let raw₀ : OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j₀ := by
    simp only [OracleStatement, j₀, zero_mul, Fin.mk_zero']
    exact firstOracleEncoding K β t
  exact fun j => if hj : j₀ = j then hj ▸ raw₀ else fun _ => 0

private theorem mp_mpr_cancel {α β : Type} (h : α = β) (x : β) : h.mp (h.mpr x) = x := by
  cases h
  rfl

/-- Reading the honest initial oracle family returns the encoded codeword. -/
@[simp]
theorem getFirstOracle_honestInitialOracleStatement (t : MultilinearPoly L ℓ) :
    getFirstOracle K β (honestInitialOracleStatement K β ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t) = firstOracleEncoding K β t := by
  simp only [getFirstOracle, honestInitialOracleStatement, dif_pos rfl]
  exact mp_mpr_cancel _ _

/-- Honest coverage uses the same oracle family and accessor as the production relation. -/
theorem honestInitialOracleStatement_consistent (t : MultilinearPoly L ℓ) :
    firstOracleWitnessConsistencyProp K β t
      (getFirstOracle K β (honestInitialOracleStatement K β ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t)) := by
  rw [getFirstOracle_honestInitialOracleStatement]
  exact firstOracleWitnessConsistencyProp_honest K β t

end Binius.BinaryBasefold

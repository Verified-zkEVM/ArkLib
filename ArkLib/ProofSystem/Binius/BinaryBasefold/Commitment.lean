/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility

/-!
# Binding of the initial Binary Basefold oracle

The initial compatibility predicate uses strict half-minimum-distance closeness to the
encoding of a multilinear polynomial. Polynomial root counting, novel-basis coordinates and
Boolean evaluation identify a source from its encoding. The Hamming triangle inequality then
proves functionality, while exact encodings supply honest coverage. The shared first-oracle
interface packages exact and unique-radius compatibility.
-/

@[expose] public section

noncomputable section
namespace Binius.BinaryBasefold

open RingSwitching

open AdditiveNTT Polynomial MvPolynomial Module Code

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) :=
  ⟨CharP.prime_ringChar K⟩
variable [Fintype K] [DecidableEq K]
  [Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡] {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- The initial novel-basis encoding, evaluated on the initial code domain. -/
def firstOracleEncoding (t : MultilinearPoly L ℓ) :
    sDomain K β h_ℓ_add_R_rate 0 → L :=
  polyToOracleFunc K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0)
    (polynomialFromNovelCoeffsF₂ K β ℓ (by omega)
      (fun ω => t.val.eval (bitsOfIndex ω)))

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero ℓ] [NeZero 𝓡] in
/-- Novel coefficients are coordinates in the novel polynomial basis. -/
private theorem polynomialFromNovelCoeffsF₂_eq_novelPolynomialBasis_equivFun_symm
    (hle : ℓ ≤ r) (a : Fin (2 ^ ℓ) → L) :
    polynomialFromNovelCoeffsF₂ K β ℓ hle a =
      (novelPolynomialBasis K β ℓ hle).equivFun.symm a := by
  apply Subtype.ext
  rw [Basis.equivFun_symm_apply]
  simp [novelPolynomialBasis_is_basisVectors, basisVectors,
    polynomialFromNovelCoeffsF₂, polynomialFromNovelCoeffs, Polynomial.smul_eq_C_mul]

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero ℓ] [NeZero 𝓡] in
/-- Distinct multilinear sources have distinct initial encoding tables. -/
theorem firstOracleEncoding_injective :
    Function.Injective (firstOracleEncoding K β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  intro t u h
  let P := polynomialFromNovelCoeffsF₂ K β ℓ (by omega) (fun ω => t.val.eval (bitsOfIndex ω))
  let Q := polynomialFromNovelCoeffsF₂ K β ℓ (by omega) (fun ω => u.val.eval (bitsOfIndex ω))
  have hcard : 2 ^ ℓ ≤ Fintype.card (sDomain K β h_ℓ_add_R_rate (0 : Fin r)) := by
    by_cases hzero : ℓ = 0
    · conv_lhs => rw [hzero, pow_zero]
      exact Fintype.card_pos
    · rw [sDomain_card K β h_ℓ_add_R_rate 0 (by simp; omega),
        (show Fintype.card K = 2 from Fact.out)]
      simp only [Fin.val_zero, Nat.sub_zero]
      exact Nat.pow_le_pow_right (by decide) (Nat.le_add_right ℓ 𝓡)
  have hP : (P : L[X]) = Q := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P : L[X]) (Q : L[X])
      (f := fun x : sDomain K β h_ℓ_add_R_rate (0 : Fin r) => (x : L)) Subtype.val_injective
      (by intro x; simpa only [firstOracleEncoding, polyToOracleFunc, P, Q] using congrFun h x)
    exact (max_lt (ReedSolomon.natDegree_lt_of_mem_degreeLT P.property)
      (ReedSolomon.natDegree_lt_of_mem_degreeLT Q.property)).trans_le hcard
  have hcoeff : (fun ω : Fin (2 ^ ℓ) => t.val.eval (bitsOfIndex ω)) =
      (fun ω => u.val.eval (bitsOfIndex ω)) := by
    apply (novelPolynomialBasis K β ℓ (by omega)).equivFun.symm.injective
    rw [← polynomialFromNovelCoeffsF₂_eq_novelPolynomialBasis_equivFun_symm K β (by omega),
      ← polynomialFromNovelCoeffsF₂_eq_novelPolynomialBasis_equivFun_symm K β (by omega)]
    exact Subtype.ext hP
  apply (MvPolynomial.MLEEquivFin (R := L) (n := ℓ)).injective
  funext ω
  dsimp [MvPolynomial.MLEEquivFin, MvPolynomial.MLEEquiv]
  have hω : finFunctionFinEquiv (finFunctionFinEquiv.symm ω) = ω := by simp
  rw [← hω]
  rw [Equiv.piCongr_apply_apply, Equiv.piCongr_apply_apply]
  simp only [Equiv.refl_apply]
  have hbits : (fun i => ((finFunctionFinEquiv.symm ω i : Fin 2) : L)) =
      bitsOfIndex (L := L) ω := coe_fin_pow_two_eq_bitsOfIndex (L := L) (k := ω)
  rw [hbits]
  exact congrFun hcoeff ω

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero ℓ] [NeZero 𝓡] in
/-- One first oracle can be compatible with only one packed polynomial. -/
theorem firstOracleWitnessConsistent_functional
    (f : sDomain K β h_ℓ_add_R_rate (0 : Fin r) → L) (t u : MultilinearPoly L ℓ)
    (ht : FirstOracleWitnessConsistent K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t f)
    (hu : FirstOracleWitnessConsistent K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) u f) : t = u := by
  apply firstOracleEncoding_injective K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  have hmem (v : MultilinearPoly L ℓ) :
      firstOracleEncoding K β v ∈ code K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 :=
    (polynomialCodeword K β 0
      (polynomialFromNovelCoeffsF₂ K β ℓ (by omega)
        (fun ω => v.val.eval (bitsOfIndex ω)))).property
  apply Code.eq_of_lt_dist (hmem t) (hmem u)
  have htri := hammingDist_triangle (firstOracleEncoding K β t) f (firstOracleEncoding K β u)
  rw [hammingDist_comm (firstOracleEncoding K β t) f] at htri
  change 2 * hammingDist f (firstOracleEncoding K β t) < codeDistance K β 0 at ht
  change 2 * hammingDist f (firstOracleEncoding K β u) < codeDistance K β 0 at hu
  change hammingDist (firstOracleEncoding K β t) (firstOracleEncoding K β u) < codeDistance K β 0
  omega

omit [DecidableEq K]  [Fact (β 0 = 1)] [NeZero ℓ] [NeZero 𝓡] in
/-- The exact initial encoding is compatible with its source polynomial. -/
theorem firstOracleWitnessConsistent_firstOracleEncoding (t : MultilinearPoly L ℓ) :
    FirstOracleWitnessConsistent K β t
      (firstOracleEncoding K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t) := by
  classical
  change 2 * hammingDist (firstOracleEncoding K β t) (firstOracleEncoding K β t) <
    codeDistance K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
  rw [hammingDist_self, mul_zero]
  exact codeDistance_pos K β 0

variable (ϑ : ℕ) [NeZero ϑ] [Fact (ϑ ∣ ℓ)]

/-- The initial oracle family contains the honest first codeword. -/
def honestInitialOracleStatement (t : MultilinearPoly L ℓ) :
    ∀ j, OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j := by
  let j₀ : Fin (toOutCodewordsCount ℓ ϑ 0) := ⟨0, by
    rw [toOutCodewordsCount_zero]
    omega⟩
  let raw₀ : OracleStatement K β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ 0 j₀ := by
    simpa only [OracleStatement, oraclePositionToDomainIndex, j₀, Fin.val_zero, zero_mul,
      Fin.mk_zero'] using firstOracleEncoding K β t
  exact fun j => if hj : j₀ = j then hj ▸ raw₀ else fun _ => 0

private theorem cast_function_apply {α β γ : Type} (h : α = β)
    (hfun : (β → γ) = (α → γ)) (f : α → γ) (x : α) :
    hfun.mpr f (cast h x) = f x := by
  cases h
  cases hfun
  rfl

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero 𝓡] in
/-- The first-oracle accessor reads the original encoded polynomial. -/
@[simp] theorem getFirstOracle_honestInitialOracleStatement (t : MultilinearPoly L ℓ) :
    getFirstOracle K β (honestInitialOracleStatement K β ϑ
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t) = firstOracleEncoding K β t := by
  funext y
  simp only [getFirstOracle, honestInitialOracleStatement, dite_eq_left rfl]
  exact cast_function_apply _ _ _ _

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero 𝓡] in
/-- The complete honest oracle family is compatible with its source polynomial. -/
theorem firstOracleWitnessConsistent_getFirstOracle_honestInitialOracleStatement
    (t : MultilinearPoly L ℓ) :
    FirstOracleWitnessConsistent K β t
      (getFirstOracle K β (honestInitialOracleStatement K β ϑ
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t)) := by
  rw [getFirstOracle_honestInitialOracleStatement]
  exact firstOracleWitnessConsistent_firstOracleEncoding K β t

/-- The first-oracle interface with exact and unique-radius compatibility relations. -/
def firstOracleInterface : AbstractOStmtIn L ℓ where
  ιₛᵢ := Fin (toOutCodewordsCount ℓ ϑ 0)
  OStmtIn := OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0
  Oₛᵢ := instOracleStatementBinaryBasefold K β
  initialCompatibility := fun x =>
    FirstOracleWitnessConsistent K β x.1 (getFirstOracle K β x.2)
  strictInitialCompatibility := fun x =>
    getFirstOracle K β x.2 = firstOracleEncoding K β x.1
  strictInitialCompatibility_implies_initialCompatibility o t h := by
    change FirstOracleWitnessConsistent K β t (getFirstOracle K β o)
    rw [h]
    exact firstOracleWitnessConsistent_firstOracleEncoding K β t

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero 𝓡] in
/-- Unique-radius compatibility determines the committed polynomial. -/
theorem firstOracleInterface_functional :
    (firstOracleInterface K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Functional := by
  intro ost t u ht hu
  exact firstOracleWitnessConsistent_functional K β _ t u ht hu

omit [DecidableEq K] [Fact (β 0 = 1)] [NeZero 𝓡] in
/-- Every source has an exact first-oracle encoding in this interface. -/
theorem firstOracleInterface_strictInitialCompatibility_honest (t : MultilinearPoly L ℓ) :
    (firstOracleInterface K β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).strictInitialCompatibility
      (t, honestInitialOracleStatement K β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t) :=
  getFirstOracle_honestInitialOracleStatement K β ϑ t

end Binius.BinaryBasefold

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

set_option maxHeartbeats 400000  -- Increase if needed
set_option profiler true
set_option profiler.threshold 50  -- Show anything taking over 10ms

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

noncomputable section SoundnessTools

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}

/-!
### Binary Basefold Specific Code Definitions

Definitions specific to the Binary Basefold protocol based on the fundamentals document.
-/

/-- The Reed-Solomon code C^(i) for round i in Binary Basefold.
For each i ∈ {0, steps, ..., ℓ}, C(i) is the Reed-Solomon code
RS_{L, S⁽ⁱ⁾}[2^{ℓ+R-i}, 2^{ℓ-i}]. -/
def BBF_Code (i : Fin r) :
  Submodule L ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L) :=
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) i ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  ReedSolomon.code (domain := domain) (deg := 2^(ℓ - i.val))

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma exists_BBF_poly_of_codeword (i : Fin r)
  (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  ∃ P : L⦃<2^(ℓ-i)⦄[X], polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P) = u := by
  have h_u_mem := u.property
  unfold BBF_Code at h_u_mem
  simp only [code, evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mem_map] at h_u_mem
  -- We use the same logic you had, but we return the Subtype explicitly
  obtain ⟨P_raw, hP_raw⟩ := h_u_mem
  -- Construct the subtype element
  let P : L⦃<2^(ℓ-i)⦄[X] := ⟨P_raw, hP_raw.1⟩
  use P
  -- Prove the evaluation part
  exact hP_raw.2

def getBBF_Codeword_poly (i : Fin r)
  (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) : L⦃<2^(ℓ-i)⦄[X] :=
  Classical.choose (exists_BBF_poly_of_codeword 𝔽q β i u)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma getBBF_Codeword_poly_spec (i : Fin r)
  (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  u = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i)
    (P := getBBF_Codeword_poly 𝔽q β i u) := by
  let res := Classical.choose_spec (exists_BBF_poly_of_codeword 𝔽q β i u)
  exact id (Eq.symm res)

def getBBF_Codeword_of_poly (i : Fin r) (h_i : i ≤ ℓ) (P : L⦃< 2 ^ (ℓ - i)⦄[X]) :
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P)
  have h_g_mem : g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
    unfold BBF_Code
    simp only [code, evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk,
      AddHom.coe_mk, Submodule.mem_map]
    use P
    constructor
    · simp only [SetLike.coe_mem]
    · funext y
      exact rfl
  exact ⟨g, h_g_mem⟩

/-- The (minimum) distance d_i of the code C^(i) : `dᵢ := 2^(ℓ + R - i) - 2^(ℓ - i) + 1` -/
abbrev BBF_CodeDistance (i : Fin r) : ℕ :=
  ‖((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L))‖₀

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
lemma BBF_CodeDistance_eq (i : Fin r) (h_i : i ≤ ℓ) :
  BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    = 2^(ℓ + 𝓡 - i.val) - 2^(ℓ - i.val) + 1 := by
  unfold BBF_CodeDistance
  -- Create the embedding from domain elements to L
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) i ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  -- Create α : Fin m → L by composing with an equivalence
  let m := Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) i)
  have h_dist_RS := ReedSolomonCode.dist_eq' (F := L) (ι := (sDomain 𝔽q β h_ℓ_add_R_rate)
    (i := i)) (α := domain) (n := 2^(ℓ - i.val)) (h := by
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := Sdomain_bound (by omega))]
      rw [hF₂.out];
      apply Nat.pow_le_pow_right (hx := by omega); omega
    )
  unfold BBF_Code
  rw [h_dist_RS]
  rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := Sdomain_bound (by omega)), hF₂.out]

/-- Disagreement set Δ : The set of points where two functions disagree.
For functions f^(i) and g^(i), this is {y ∈ S^(i) | f^(i)(y) ≠ g^(i)(y)}. -/
def disagreementSet (i : Fin r) (h_i : i ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) i) := {y | f y ≠ g y}

/-- Fiber-wise disagreement set Δ^(i) : The set of points y ∈ S^(i+ϑ) for which
functions f^(i) and g^(i) are not identical when restricted to the entire fiber
of points in S⁽ⁱ⁾ that maps to y. -/
def fiberwiseDisagreementSet (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :=
  -- The set of points `y ∈ S^{i+steps}` that there exists a
    -- point `x` in its fiber where `f x ≠ g x`
  {y | ∃ x, (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
    (k := steps) h_destIdx h_destIdx_le x) = y ∧ f x ≠ g x}

def pair_fiberwiseDistance (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : ℕ :=
    (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g).card

/-- Fiber-wise distance d^(i) : The minimum size of the fiber-wise disagreement set
between f^(i) and any codeword in C^(i). -/
def fiberwiseDistance (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : ℕ :=
  -- The minimum size of the fiber-wise disagreement set between f^(i) and any codeword in C^(i)
  -- d^(i)(f^(i), C^(i)) := min_{g^(i) ∈ C^(i)} |Δ^(i)(f^(i), g^(i))|
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  let disagreement_sizes := (fun (g : C_i) =>
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      steps h_destIdx h_destIdx_le (f := f) (g := g)
  ) '' Set.univ
  sInf disagreement_sizes

/-- Fiberwise closeness : f^(i) is fiberwise close to C^(i) if
2 * d^(i)(f^(i), C^(i)) < d_{i+steps} -/
def fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i) : Prop :=
  let left := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)
  2 * (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx): ℕ∞)

def pair_fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
    2 * pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps
      h_destIdx h_destIdx_le (f := f) (g := g) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx): ℕ∞)

/-- Hamming UDR-closeness : f is close to C in Hamming distance if `2 * d(f, C) < d_i` -/
def UDRClose (i : Fin r) (h_i : i ≤ ℓ) (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Prop :=
    2 * Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

def pair_UDRClose (i : Fin r) (h_i : i ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * Δ₀(f, g) < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

section ConstantFunctions

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma constFunc_mem_BBFCode {i : Fin r} (h_i : i ≤ ℓ) (c : L) :
  (fun _ => c) ∈ (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i))
  := by
  unfold BBF_Code
  simp only
  simp only [code, evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mem_map]
  use Polynomial.C c
  constructor
  · rw [Polynomial.mem_degreeLT]
    apply lt_of_le_of_lt (Polynomial.degree_C_le)
    norm_num
  · ext x; simp only [Polynomial.eval_C]

lemma constFunc_UDRClose {i : Fin r} (h_i : i ≤ ℓ) (c : L) :
  UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i (fun _ => c) := by
  sorry

end ConstantFunctions
omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 in
lemma UDRClose_iff_within_UDR_radius (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f ↔
    Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≤
      uniqueDecodingRadius (ι := (sDomain 𝔽q β h_ℓ_add_R_rate i))
        (F := L) (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  unfold UDRClose
  let card_Sᵢ := sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := Sdomain_bound (by omega))
  conv_rhs =>
    unfold BBF_Code;
    rw [ReedSolomonCode.uniqueDecodingRadius_RS_eq' (h := by
      rw [card_Sᵢ, hF₂.out]; apply Nat.pow_le_pow_right (hx := by omega); omega
    )];
  simp_rw [card_Sᵢ, hF₂.out, BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)]
  simp only [cast_add, ENat.coe_sub, cast_pow, cast_ofNat, cast_one]
  constructor

  · intro h_UDRClose
    -- 1. Prove distance is finite
    -- The hypothesis implies 2 * Δ₀ is finite, so Δ₀ must be finite.
    have h_finite : Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≠ ⊤ := by
      intro h_top
      rw [h_top] at h_UDRClose
      exact not_top_lt h_UDRClose
    -- 2. Lift to Nat to use standard arithmetic
    lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
      using h_finite with d_nat h_eq
    dsimp only [BBF_Code] at h_eq
    simp_rw [←h_eq]
    -- ⊢ ↑d_nat ≤ ↑((2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i)) / 2)
    have h_lt : 2 * d_nat < 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 := by
      norm_cast at h_UDRClose ⊢ -- both h_UDRClose and ⊢ are in ENat
    simp only [Nat.cast_le]
    have h_le := Nat.le_of_lt_succ (m := 2 * d_nat) (n := 2^(ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) ) h_lt
    rw [Nat.mul_comm 2 d_nat] at h_le
    rw [←Nat.le_div_iff_mul_le (k0 := by norm_num)] at h_le
    exact h_le
  · intro h_within
    -- 1. Prove finite
    have h_finite : Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≠ ⊤ := by
      intro h_top
      unfold BBF_Code at h_top
      simp only [h_top, top_le_iff, ENat.coe_ne_top] at h_within

    -- 2. Lift to Nat
    lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
      using h_finite with d_nat h_eq

    unfold BBF_Code at h_eq
    rw [←h_eq] at h_within
    norm_cast at h_within ⊢
    -- now both h_within and ⊢ are in ENat, equality can be converted
    omega

/-- Unique closest codeword in the unique decoding radius of a function f -/
@[reducible, simp]
def UDRCodeword (i : Fin r) (h_i : i ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
   := by
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  )
  -- h_ExistsUnique : ∃! v, v ∈ ↑(BBF_Code 𝔽q β i)
    -- ∧ Δ₀(f, v) ≤ Code.uniqueDecodingRadius ↑(BBF_Code 𝔽q β i)
  exact (Classical.choose h_ExistsUnique)

lemma UDRCodeword_constFunc_eq_self (i : Fin r) (h_i : i ≤ ℓ) (c : L) :
  UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_i (f := fun _ => c)
    (h_within_radius := by apply constFunc_UDRClose) = fun _ => c := by
  sorry

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 in
lemma UDRCodeword_mem_BBF_Code (i : Fin r) (h_i : i ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_within_radius) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  unfold UDRCodeword
  simp only [Fin.eta, SetLike.mem_coe, and_imp]
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  )
  let res := (Classical.choose_spec h_ExistsUnique).1.1
  simp only [SetLike.mem_coe, and_imp] at res
  exact res

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 in
lemma dist_to_UDRCodeword_le_uniqueDecodingRadius (i : Fin r) (h_i : i ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  Δ₀(f, UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_within_radius) ≤
    uniqueDecodingRadius (ι := (sDomain 𝔽q β h_ℓ_add_R_rate i))
      (F := L) (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  ) -- res : ∃! v, v ∈ ↑(BBF_Code 𝔽q β i) ∧ Δ₀(f, v) ≤ uniqueDecodingRadius ↑(BBF_Code 𝔽q β i)
  let res := (Classical.choose_spec h_ExistsUnique).1
  simp only [Fin.eta, SetLike.mem_coe, and_imp] at res
  let h_close := res.2
  unfold UDRCodeword
  simp only [Fin.eta, SetLike.mem_coe, and_imp, ge_iff_le]
  exact h_close

/-- Computational version of `UDRCodeword`, where we use the Berlekamp-Welch decoder to extract
the closest codeword within the unique decoding radius of a function `f` -/
def extractUDRCodeword
  (i : Fin r) (h_i : i ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i)
   := by
  -- Set up Berlekamp-Welch parameters
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate i)
  set d := Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
  let e : ℕ := d.toNat
  have h_dist_ne_top : d ≠ ⊤ := by
    intro h_dist_eq_top
    unfold UDRClose at h_within_radius
    unfold d at h_dist_eq_top
    simp only [h_dist_eq_top, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENat.mul_top,
      not_top_lt] at h_within_radius
  let k : ℕ := 2^(ℓ - i.val)  -- degree bound from BBF_Code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
    i ≃ Fin domain_size := by
    simp only [domain_size]
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := Sdomain_bound h_i)]
    have h_equiv := sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate (i := i) (Sdomain_bound h_i)
    convert h_equiv
    exact hF₂.out
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := Sdomain_bound h_i)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  let berlekamp_welch_result : Option L[X] := BerlekampWelch.decoder (F := L) e k ωs f_vals
  have h_ne_none : berlekamp_welch_result ≠ none := by
    -- 1) Choose a codeword achieving minimal Hamming distance (closest codeword).
    let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    let S := (fun (g : C_i) => Δ₀(f, g)) '' Set.univ
    let SENat := (fun (g : C_i) => (Δ₀(f, g) : ENat)) '' Set.univ
      -- let S_nat := (fun (g : C_i) => hammingDist f g) '' Set.univ
    have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
      rw [ENat.coe_sInf (hs := hS_nonempty)]
      simp only [SENat, Set.image_univ, sInf_range]
      simp only [S, Set.image_univ, iInf_range]
    rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
    rcases g_subtype with ⟨g_closest, hg_mem⟩
    have h_dist_f : hammingDist f g_closest ≤ e := by
      rw [show e = d.toNat from rfl]
      -- The distance `d` is exactly the Hamming distance of `f` to `g_closest` (lifted to `ℕ∞`).
      have h_dist_eq_hamming : d = (hammingDist f g_closest) := by
        -- We found `g_closest` by taking the `sInf` of all distances, and `hg_min`
        -- shows that the distance to `g_closest` achieves this `sInf`.
        have h_distFromCode_eq_sInf : d = sInf SENat := by
          apply le_antisymm
          · -- Part 1 : `d ≤ sInf ...`
            simp only [d, distFromCode]
            apply sInf_le_sInf
            intro a ha
            -- `a` is in `SENat`, so `a = ↑Δ₀(f, g)` for some codeword `g`.
            rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
            -- We must show `a` is in the set for `d`, which is `{d' | ∃ v, ↑Δ₀(f, v) ≤ d'}`.
            -- We can use `g` itself as the witness `v`, since `↑Δ₀(f, g) ≤ ↑Δ₀(f, g)`.
            use g; simp only [Fin.eta, Subtype.coe_prop, le_refl, and_self]
          · -- Part 2 : `sInf ... ≤ d`
            simp only [d, distFromCode]
            apply le_sInf
            -- Let `d'` be any element in the set that `d` is the infimum of.
            intro d' h_d'
            -- Unpack `h_d'` : there exists some `v` in the code such that
            -- `↑(hammingDist f v) ≤ d'`.
            rcases h_d' with ⟨v, hv_mem, h_dist_v_le_d'⟩
            -- By definition, `sInf SENat` is a lower bound for all elements in `SENat`.
            -- The element `↑(hammingDist f v)` is in `SENat`.
            have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist f v) := by
              apply sInf_le -- ⊢ ↑Δ₀(f, v) ∈ SENat
              rw [Set.mem_image]
              -- ⊢ ∃ x ∈ Set.univ, ↑Δ₀(f, ↑x) = ↑Δ₀(f, v)
              simp only [Fin.eta, Set.mem_univ, Nat.cast_inj, true_and, Subtype.exists, exists_prop]
              -- ⊢ ∃ a ∈ C_i, Δ₀(f, a) = Δ₀(f, v)
              use v
              exact And.symm ⟨rfl, hv_mem⟩
            -- Now, chain the inequalities : `sInf SENat ≤ ↑(dist_to_any_v) ≤ d'`.
            exact h_sInf_le_dist_v.trans h_dist_v_le_d'
        rw [h_distFromCode_eq_sInf, ←h_coe_sinfS_eq_sinfSENat, ←hg_min]
      rw [h_dist_eq_hamming]
      rw [ENat.toNat_coe]
    -- Get the closest polynomial
    obtain ⟨p, hp_deg_lt : p ∈ L[X]_k, hp_eval⟩ : ∃ p, p ∈ Polynomial.degreeLT L k ∧
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := i)) ↦ p.eval (↑x)) = g_closest := by
      simp only [Fin.eta, BBF_Code, code, evalOnPoints, Function.Embedding.coeFn_mk,
        Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk, C_i] at hg_mem
      rcases hg_mem with ⟨p_witness, hp_prop, hp_eq⟩
      use p_witness
    have natDeg_p_lt_k : p.natDegree < k := by
      simp only [mem_degreeLT] at hp_deg_lt
      by_cases hi : i = ℓ
      · simp only [hi, tsub_self, pow_zero, cast_one, lt_one_iff, k] at ⊢ hp_deg_lt
        by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
        · rw [Polynomial.natDegree_eq_of_degree_eq_some]
          have h_deg_p : p.degree = 0 := by
            have h_le_zero : p.degree ≤ 0 := by
              exact WithBot.lt_one_iff_le_zero.mp hp_deg_lt
            have h_deg_ne_bot : p.degree ≠ ⊥ := by
              rw [Polynomial.degree_ne_bot]; omega
            apply le_antisymm h_le_zero (zero_le_degree_iff.mpr hp_p_eq_0)
          simp only [h_deg_p, CharP.cast_eq_zero]
      · by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
          have h_i_lt_ℓ : i < ℓ := by omega
          simp only [ofNat_pos, pow_pos, k]
        · rw [Polynomial.natDegree_lt_iff_degree_lt (by omega)]
          exact hp_deg_lt
    have h_decoder_succeeds : BerlekampWelch.decoder e k ωs f_vals = some p := by
      apply BerlekampWelch.decoder_eq_some
      · -- ⊢ `2 * e < d_i = n - k + 1`
        have h_le: 2 * e ≤ domain_size - k := by
          have hS_card_eq_domain_size := sDomain_card 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := Sdomain_bound (by omega))
          simp only [domain_size, k]; simp_rw [hS_card_eq_domain_size, hF₂.out]
          unfold UDRClose at h_within_radius
          rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)] at h_within_radius
          -- h_within_radius : 2 * Δ₀(f, ↑(BBF_Code 𝔽q β i))
            -- < ↑(2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1)
          dsimp only [Fin.eta, e, d]
          lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
            using h_dist_ne_top with d_nat h_eq
          norm_cast at h_within_radius
          simp only [ENat.toNat_coe, ge_iff_le]
          omega
        omega
      · -- ⊢ `k ≤ domain_size`. This holds by the problem setup.
        simp only [k, domain_size]
        rw [sDomain_card 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := Sdomain_bound (by omega)), hF₂.out]
        apply Nat.pow_le_pow_right (by omega) -- ⊢ ℓ - ↑i ≤ ℓ + 𝓡 - ↑⟨↑i, ⋯⟩
        simp only [tsub_le_iff_right]
        omega
      · -- ⊢ Function.Injective ωs
        simp only [ωs]
        -- The composition of two injective functions (`Equiv.symm` and `Subtype.val`) is injective.
        exact Function.Injective.comp Subtype.val_injective (Equiv.injective _)
      · -- ⊢ `p.natDegree < k`. This is true from `hp_deg`.
        exact natDeg_p_lt_k
      · -- ⊢ `Δ₀(f_vals, (fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e`
        change hammingDist f_vals ((fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e
        simp only [ωs]
        have h_functions_eq : (fun a ↦ Polynomial.eval a p) ∘ ωs
          = g_closest ∘ domain_to_fin.symm := by
          ext j; simp only [Function.comp_apply, Fin.eta, ωs]
          rw [←hp_eval]
        rw [h_functions_eq]
        -- ⊢ Δ₀(f_vals, g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        simp only [Fin.eta, ge_iff_le, f_vals]
        -- ⊢ Δ₀(fun j ↦ f (domain_to_fin.symm j), g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        calc
          _ ≤ hammingDist f g_closest := by
            apply hammingDist_le_of_outer_comp_injective f g_closest domain_to_fin.symm
              (hg := by exact Equiv.injective domain_to_fin.symm)
          _ ≤ e := by exact h_dist_f
    simp only [ne_eq, berlekamp_welch_result]
    simp only [h_decoder_succeeds, reduceCtorEq, not_false_eq_true]
  let p : L[X] := berlekamp_welch_result.get (Option.ne_none_iff_isSome.mp h_ne_none)
  exact fun x => p.eval x.val

omit [CharP L 2] in
/-- `Δ₀(f, g) ≤ pair_fiberwiseDistance(f, g) * 2 ^ steps` -/
lemma hammingDist_le_fiberwiseDistance_mul_two_pow_steps (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i):
    Δ₀(f, g) ≤ (pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      steps h_destIdx h_destIdx_le (f := f) (g := g)) * 2 ^ steps := by
  let d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le (f := f) (g := g)
  have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g) ≤ d_fw * 2 ^ steps := by
    -- This proves `dist f g ≤ (fiberwiseDisagreementSet ... f g).ncard * 2 ^ steps`
    -- and lifts to ℕ∞. We prove the `Nat` version `hammingDist f g ≤ ...`,
    -- which is equivalent.
    -- Let ΔH be the finset of actually bad x points where f and g disagree.
    set ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    have h_dist_eq_card : hammingDist f g = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq_card]
    -- Y_bad is the set of quotient points y that THERE EXISTS a bad fiber point x
    set Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g
    simp only at * -- simplify domain indices everywhere
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    have hFinType_Y_bad : Fintype Y_bad := by exact Fintype.ofFinite ↑Y_bad
    -- Every point of disagreement `x` must belong to a fiber over some `y` in `Y_bad`,
    -- BY DEFINITION of `Y_bad`. Therefore, `ΔH` is a subset of the union of the fibers
    -- of `Y_bad`
    have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Finset.biUnion Y_bad
        (t := fun y => ((qMap_total_fiber 𝔽q β (i := i) (steps := steps)
          h_destIdx h_destIdx_le (y := y)) ''
          (Finset.univ : Finset (Fin ((2:ℕ)^steps)))).toFinset) := by
      -- ⊢ If any x ∈ ΔH, then x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      intro x hx_in_ΔH; -- ⊢ x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      simp only [ΔH, Finset.mem_filter] at hx_in_ΔH
      -- Now we actually apply iterated qMap into x to get y_of_x,
      -- then x ∈ qMap_total_fiber(y_of_x) by definition
      let y_of_x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) h_destIdx h_destIdx_le x
      apply Finset.mem_biUnion.mpr; use y_of_x
      -- ⊢ y_of_x ∈ Y_bad.toFinset ∧ x ∈ qMap_total_fiber(y_of_x)
      have h_elemenet_Y_bad :  y_of_x ∈ Y_bad := by
        -- ⊢ y ∈ Y_bad
        simp only [fiberwiseDisagreementSet, iteratedQuotientMap, ne_eq, Subtype.exists, mem_filter,
          mem_univ, true_and, Y_bad]
        -- one bad fiber point of y_of_x is x itself
        let XX := x.val
        have h_XX_in_source : XX ∈ sDomain 𝔽q β h_ℓ_add_R_rate (i := i) := by
          exact Submodule.coe_mem x
        use XX
        use h_XX_in_source
        -- ⊢ Ŵ_steps⁽ⁱ⁾(XX) = y (iterated quotient map) ∧ ¬f ⟨XX, ⋯⟩ = g ⟨XX, ⋯⟩
        have h_forward_iterated_qmap : Polynomial.eval XX
            (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate i
              (k := steps) (h_k := by omega)) = y_of_x := by
          simp only [iteratedQuotientMap, XX, y_of_x];
        have h_eval_diff : f ⟨XX, by omega⟩ ≠ g ⟨XX, by omega⟩ := by
          unfold XX
          simp only [Subtype.coe_eta, ne_eq, hx_in_ΔH, not_false_eq_true]
        simp only [h_forward_iterated_qmap, Subtype.coe_eta, h_eval_diff,
          not_false_eq_true, and_self]
      simp only [h_elemenet_Y_bad, true_and]

      set qMapFiber := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
        h_destIdx h_destIdx_le (y := y_of_x)
      simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ, true_and]
      use (pointToIterateQuotientIndex (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x))
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (x := x) (y := y_of_x).mp (by rfl)
      exact h_res
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    -- The cardinality of a subset is at most the cardinality of the superset.
    apply (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans
    -- The cardinality of a disjoint union is the sum of cardinalities.
    rw [Finset.card_biUnion]
    · -- The size of the sum is the number of bad fibers (`Y_bad.ncard`) times
      -- the size of each fiber (`2 ^ steps`).
      simp only [Set.toFinset_card]
      have h_card_fiber_per_quotient_point := card_qMap_total_fiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      simp only [Set.image_univ, Fintype.card_ofFinset,
        Subtype.forall] at h_card_fiber_per_quotient_point
      have h_card_fiber_of_each_y : ∀ y ∈ Y_bad,
          Fintype.card ((qMap_total_fiber 𝔽q β (i := i) (steps := steps)
            h_destIdx h_destIdx_le (y := y)) ''
            ↑(Finset.univ : Finset (Fin ((2:ℕ)^steps)))) = 2 ^ steps := by
        intro y hy_in_Y_bad
        have hy_card_fiber_of_y := h_card_fiber_per_quotient_point (a := y) (b := by
          exact Submodule.coe_mem y)
        simp only [coe_univ, Set.image_univ, Fintype.card_ofFinset, hy_card_fiber_of_y]
      rw [Finset.sum_congr rfl h_card_fiber_of_each_y]
      -- ⊢ ∑ x ∈ Y_bad.toFinset, 2 ^ steps ≤ Y_bad.encard.toNat * 2 ^ steps
      simp only [sum_const, smul_eq_mul, ofNat_pos, pow_pos, _root_.mul_le_mul_right, ge_iff_le]
      -- ⊢ Fintype.card ↑Y_bad ≤ Nat.card ↑Y_bad
      simp only [Y_bad, d_fw, pair_fiberwiseDistance, le_refl]
    · -- Prove that the fibers for distinct quotient points y₁, y₂ are disjoint.
      intro y₁ hy₁ y₂ hy₂ hy_ne
      have h_disjoint := qMap_total_fiber_disjoint (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y₁ := y₁) (y₂ := y₂) (hy_ne := hy_ne)
      simp only [Function.onFun, coe_univ]
      exact h_disjoint
  exact h_dist_le_fw_dist_times_fiber_size

omit [CharP L 2] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, g⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, g⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
lemma pairUDRClose_of_pairFiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_dist_lt : pair_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f g) :
    pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (by omega) (f := f)
      (g := g) := by
  unfold pair_fiberwiseClose at h_fw_dist_lt
  norm_cast at h_fw_dist_lt
  unfold pair_UDRClose
  set d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le (f := f) (g := g)
  set d_cur := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
  -- d_cur = 2 ^ (ℓ + 𝓡 - i) - 2 ^ (ℓ - i) + 1
  set d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx)
  -- d_next = 2 ^ (ℓ + 𝓡 - (i + steps)) - 2 ^ (ℓ - (i + steps)) + 1

  have h_le : 2 * Δ₀(f, g) ≤ 2 * (d_fw * 2 ^ steps) := by
    apply Nat.mul_le_mul_left
    apply hammingDist_le_fiberwiseDistance_mul_two_pow_steps
  -- h_fw_dist_lt : 2 * d_fw < BBF_CodeDistance 𝔽q β ⟨↑i + steps, ⋯⟩
  have h_2_fw_dist_le : 2 * d_fw ≤ d_next - 1 := by omega

  have h_2_fw_dist_mul_2_pow_steps_le :
    2 * (d_fw * 2 ^ steps) ≤ (d_next * 2 ^ steps - 2 ^ steps):= by
    rw [←mul_assoc]
    conv_rhs =>
      rw (occs := [2]) [←one_mul (2 ^ steps)];
      rw [←Nat.sub_mul (n := d_next) (m := 1) (k := 2 ^ steps)];
    apply Nat.mul_le_mul_right
    exact h_2_fw_dist_le

  have h_2_fw_dist_mul_2_pow_steps_le : (d_next * 2 ^ steps - 2 ^ steps) = d_cur - 1 := by
    dsimp only [d_next, d_cur]
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega), BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)]
    simp only [add_tsub_cancel_right]
    rw [Nat.add_mul, Nat.sub_mul]
    rw [←Nat.pow_add, ←Nat.pow_add]
    have h_exp1 : ℓ + 𝓡 - destIdx + steps = ℓ + 𝓡 - i.val := by omega
    have h_exp2 : ℓ - destIdx + steps = ℓ - i.val := by omega
    rw [h_exp1, h_exp2]
    omega

  have h_le_2 : 2 * (d_fw * 2 ^ steps) ≤ BBF_CodeDistance 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) - 1:= by
    omega

  apply Nat.lt_of_le_pred (h := by simp only [d_cur]; rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)]; omega)
  simp only [pred_eq_sub_one]
  exact Nat.le_trans h_le h_le_2

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] in
lemma exists_fiberwiseClosestCodeword (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps]
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃ (g : S_i → L), g ∈ C_i ∧
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g) := by
  simp only [SetLike.mem_coe]
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  set C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  -- Let `S` be the set of all possible fiber-wise disagreement sizes.
  let S := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (g := g)).card) '' Set.univ
  -- The code `C_i` (a submodule) is non-empty, so `S` is also non-empty.
  have hS_nonempty : S.Nonempty := by
    refine Set.image_nonempty.mpr ?_

    exact Set.univ_nonempty
  -- For a non-empty set of natural numbers, `sInf` is an element of the set.
  have h_sInf_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
  -- By definition, `d_fw = sInf S`.
  -- Since `sInf S` is in the image set `S`, there must be an element `g_subtype` in the domain
  -- (`C_i`) that maps to it. This `g_subtype` is the codeword we're looking for.
  rw [Set.mem_image] at h_sInf_mem
  rcases h_sInf_mem with ⟨g_subtype, _, h_eq⟩
  -- Extract the codeword and its membership proof.
  refine ⟨g_subtype, ?_, ?_⟩
  · -- membership
    exact g_subtype.property
  · -- equality of distances
    -- `fiberwiseDistance` is defined as the infimum of `S`, so it equals `sInf S`
    -- and `h_eq` tells us that this is exactly the distance to `g_subtype`.
    -- You may need to unfold `fiberwiseDistance` here if Lean doesn't reduce it automatically.
    exact id (Eq.symm h_eq)

omit [CharP L 2] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
theorem UDRClose_of_fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
  UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f := by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold UDRClose
  -- 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑i, ⋯⟩)
  set d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_destIdx h_destIdx_le f
  let C_i := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  let d_H := Δ₀(f, C_i)
  let d_i := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
  let d_i_plus_steps := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)

  have h_d_i_gt_0 : d_i > 0 := by
    dsimp only [d_i]-- , BBF_CodeDistance] -- ⊢ 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 > 0
    have h_exp_lt : ℓ - i.val < ℓ + 𝓡 - i.val := by
      exact Nat.sub_lt_sub_right (a := ℓ) (b := ℓ + 𝓡) (c := i.val) (by omega) (by
        apply Nat.lt_add_of_pos_right; exact pos_of_neZero 𝓡)
    have h_pow_lt : 2 ^ (ℓ - i.val) < 2 ^ (ℓ + 𝓡 - i.val) := by
      exact Nat.pow_lt_pow_right (by norm_num) h_exp_lt
    rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)]
    omega

  have h_C_i_nonempty : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)

  -- 1. Relate Hamming distance `d_H` to fiber-wise distance `d_fw`.
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g').card := by
    apply exists_fiberwiseClosestCodeword

  have h_UDR_close_f_g' := pairUDRClose_of_pairFiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_destIdx h_destIdx_le (f := f) (g := g') (h_fw_dist_lt := by
      dsimp only [pair_fiberwiseClose, pair_fiberwiseDistance]; norm_cast;
      rw [←h_g'_min_card];
      exact (by norm_cast at h_fw_dist_lt)
    )
  -- ⊢ 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance 𝔽q β ⟨↑i, ⋯⟩)
  calc
    2 * Δ₀(f, C_i) ≤ 2 * Δ₀(f, g') := by
      rw [ENat.mul_le_mul_left_iff (ha := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
        (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])
      ]
      apply Code.distFromCode_le_dist_to_mem (C := C_i) (u := f) (v := g') (hv := h_g'_mem)
    _ < _ := by norm_cast -- use result from h_UDR_close_f_g'

omit [CharP L 2] in
/-- This expands `exists_fiberwiseClosestCodeword` to the case `f` is fiberwise-close to `C_i`. -/
lemma exists_unique_fiberwiseClosestCodeword_within_UDR (i : Fin r) {destIdx : Fin r}
    (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃! (g : S_i → L), (g ∈ C_i) ∧
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g)) ∧
      (g = UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f
        (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f h_fw_close))
      := by
  set d_fw := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le f
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  set S_i_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  set C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  obtain ⟨g, h_g_mem, h_g_min_card⟩ : ∃ g ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g).card := by
    apply exists_fiberwiseClosestCodeword
  set C_i_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  have h_neZero_dist_C_i_next : NeZero (‖(C_i_next : Set (S_i_next → L))‖₀) := {
    out := by
      unfold C_i_next
      simp_rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := by omega)]
      omega
  }
  have h_neZero_dist_C_i : NeZero (‖(C_i : Set (S_i → L))‖₀) := {
    out := by
      unfold C_i
      simp_rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)]
      omega
  }
  use g
  have h_f_g_UDR_close : Δ₀(f, g) ≤ Code.uniqueDecodingRadius (F := L)
    (ι := S_i) (C := C_i) := by -- This relies on `h_fw_close`
    unfold fiberwiseClose at h_fw_close
    norm_cast at h_fw_close
    rw [←Code.UDRClose_iff_two_mul_proximity_lt_d_UDR] at h_fw_close
    unfold d_fw at h_g_min_card
    rw [h_g_min_card] at h_fw_close
    rw [Code.uniqueDecodingRadius, ←Nat.two_mul_lt_iff_le_half_of_sub_one (a := #(fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g)) (h_b_pos := by exact Nat.pos_of_neZero (n := ‖(C_i_next : Set (S_i_next → L))‖₀))] at h_fw_close
    -- h_fw_close : 2 * #(fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g) < ‖↑(BBF_Code 𝔽q β ⟨↑i + steps, ⋯⟩)‖₀
    rw [Code.uniqueDecodingRadius, ←Nat.two_mul_lt_iff_le_half_of_sub_one (a := Δ₀(f,g)) (h_b_pos := by exact Nat.pos_of_neZero (n := ‖(C_i : Set (S_i → L))‖₀))]
    -- 2 * Δ₀(f, g) < ‖↑(C_i)‖₀
    let res := pairUDRClose_of_pairFiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g) (h_fw_dist_lt := by
      unfold pair_fiberwiseClose pair_fiberwiseDistance
      norm_cast
    )
    exact res

  let h_f_UDR_close := UDRClose_of_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f h_fw_close
  have h_g_eq_UDRCodeword : g = UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i (h_i := by omega) f h_f_UDR_close := by
    apply Code.eq_of_le_uniqueDecodingRadius (C := C_i) (u := f)
      (v := g) (w := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f h_f_UDR_close) (hv := h_g_mem) (hw := by apply UDRCodeword_mem_BBF_Code (i := i) (f := f) (h_within_radius := h_f_UDR_close))
      (huv := by
        -- ⊢ Δ₀(f, g) ≤ uniqueDecodingRadius ↑C_i
        exact h_f_g_UDR_close
      )
      (huw := by
        apply dist_to_UDRCodeword_le_uniqueDecodingRadius (i := i) (f := f) (h_within_radius := h_f_UDR_close)
      )
  simp only
  constructor
  · constructor
    · exact h_g_mem
    · constructor
      · exact h_g_min_card
      · -- ⊢ g = UDRCodeword 𝔽q β ⟨↑i, ⋯⟩ f ⋯
        exact h_g_eq_UDRCodeword
  · -- trivial contrapositive case
    intro y hy_mem_C_i
    rw [h_g_eq_UDRCodeword]
    rw [hy_mem_C_i.2.2]

omit [CharP L 2] in
/-- **Lemma: Single Step BBF_Code membership preservation**
It establishes that folding a codeword from the i-th code produces a codeword in the (i+1)-th code.
This relies on **Lemma 4.13** that 1-step folding advances the evaluation polynomial. -/
lemma fold_preserves_BBF_Code_membership (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) (r_chal : L) :
    (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_destIdx h_destIdx_le (f := f) (r_chal := r_chal)) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  -- 1. Unwrap the code definition to get the polynomial P
  -- BBF_Code is ReedSolomon, so f comes from some P with deg < 2^(ℓ-i)
  set C_cur := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L)) with h_C_cur
  have h_f_mem : f.val ∈ C_cur := by
    unfold C_cur
    simp only [Subtype.coe_prop]
  simp only [BBF_Code, code, C_cur] at h_f_mem
  rcases h_f_mem with ⟨P, hP_deg, hP_eval⟩ -- the poly that generates `f` on `S^(i)`
  let iNovel_coeffs : Fin (2^(ℓ - i)) → L :=
    getINovelCoeffs 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) (P := P)
  simp only [evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk, AddHom.coe_mk] at hP_eval
  simp only [SetLike.mem_coe, mem_degreeLT, cast_pow, cast_ofNat] at hP_deg
  -- ⊢ Fin (2 ^ (ℓ - ↑i)) → L
  simp only [BBF_Code, code, Submodule.mem_map]
  set new_coeffs := fun j : Fin (2^(ℓ - destIdx)) =>
  (1 - r_chal) * (iNovel_coeffs ⟨j.val * 2, by
    rw [←Nat.add_zero (j.val * 2)]
    apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx)
      (i := 0) (by omega) (by omega)
  ⟩) +
  r_chal * (iNovel_coeffs ⟨j.val * 2 + 1, by
    apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx)
      (i := 1) (by omega) (by omega)
  ⟩)
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  use P_i_plus_1
  constructor
  · -- ⊢ P_i_plus_1 ∈ L[X]_(2 ^ (ℓ - (↑i + 1)))
    apply Polynomial.mem_degreeLT.mpr
    unfold P_i_plus_1
    apply degree_intermediateEvaluationPoly_lt
  · -- ⊢ (evalOnPoints ... P_i_plus_1) = fold 𝔽q β ⟨↑i, ⋯⟩ h_i_succ_lt (↑f) r_chal
    let fold_advances_evaluation_poly_res := fold_advances_evaluation_poly 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (coeffs := iNovel_coeffs) (r_chal := r_chal)
    simp only at fold_advances_evaluation_poly_res
    funext (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    dsimp only [evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk, AddHom.coe_mk]
    -- ⊢ Polynomial.eval (↑y) P_i_plus_1 = fold 𝔽q β ⟨↑i, ⋯⟩ h_i_succ_lt (↑f) r_chal y
    unfold polyToOracleFunc at fold_advances_evaluation_poly_res
    let lhs_eq := congrFun fold_advances_evaluation_poly_res y
    conv_lhs => rw [←lhs_eq]
    -- simp only [Subtype.coe_eta]
    congr 1
    funext (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i)
    -- ⊢ Polynomial.eval (↑x) (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
      -- ⟨↑i, ⋯⟩ iNovel_coeffs) = ↑f x
    unfold intermediateEvaluationPoly iNovel_coeffs
    let res := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega) (P := P) (hP_deg := hP_deg)
    unfold intermediateEvaluationPoly at res
    rw [res]
    -- ⊢ Polynomial.eval (↑x) P = ↑f x
    exact (congrFun hP_eval x)

omit [CharP L 2] in
/-- **Lemma: Iterated BBF_Code membership preservation (Induction)**
If `f` is in BBF_Code `C^{(i)}`, then `iterated_fold f r` is in BBF_Code `C^{(i+steps)}`.
NOTE: we can potentially specifify the structure of the folded polynomial. -/
lemma iterated_fold_preserves_BBF_Code_membership (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)

    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (r_challenges : Fin steps → L) :
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f) (r_challenges := r_challenges)) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  revert destIdx h_destIdx h_destIdx_le
  induction steps generalizing i with
  | zero =>
    intro destIdx h_destIdx h_destIdx_le
    have h_i_eq_destIdx : i = destIdx := by omega
    subst h_i_eq_destIdx
    -- Base case: 0 steps. iterated_fold is identity. Code is the same.
    simp only [Fin.eta, iterated_fold, reduceAdd, Fin.coe_castSucc, Fin.val_succ, id_eq,
      Fin.reduceLast, Fin.coe_ofNat_eq_mod, reduceMod, Nat.add_zero, Subtype.coe_eta,
      Fin.dfoldl_zero, SetLike.coe_mem]
  | succ k ih =>
    intro destIdx h_destIdx h_destIdx_le
    let midIdx : Fin r := ⟨i + k, by omega⟩
    have h_midIdx : midIdx = i + k := by rfl
    -- 1. Perform k steps first
    let f_k := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := k) (destIdx := midIdx) (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f) (r_challenges := Fin.init r_challenges)
    -- 2. Apply IH: f_k is in C^{(i+k)}
    have h_fk_mem : f_k ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx := by
      exact ih (i := i) (r_challenges := Fin.init r_challenges) (destIdx := midIdx) (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f)
    set f_k_code_word : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx) :=
      ⟨f_k, h_fk_mem⟩
    -- 3. Perform the (k+1)-th fold on f_k
    rw [iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := k) (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := h_midIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges)] -- (Helper lemma needed to unroll recursion)
    -- 4. Apply the Single Step Lemma
    let res := fold_preserves_BBF_Code_membership (i := midIdx) (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := by omega)
      (f := f_k_code_word) (r_chal := r_challenges (Fin.last k))
    exact res

/--
Compliance condition (Definition 4.17) : For an index `i` that is a multiple of `steps`,
the oracle `f_i` is compliant if it's close to the code fiber-wise, the next oracle
`f_i_plus_steps` is close to its code, and their unique closest codewords are consistent
with folding.
-/
def isCompliant (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ) [NeZero steps]
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
  (challenges : Fin steps → L) : Prop :=
  ∃ (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) h_destIdx h_destIdx_le (f := f_i))
    (h_dist_next_lt : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := destIdx) (h_i := by omega) (f := f_i_plus_steps)), -- note that two lts are equal
    -- Third constraint : the DECODED codewords are consistent via the iterated_fold
    let h_dist_curr_lt := UDRClose_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps h_destIdx h_destIdx_le f_i
      (h_fw_dist_lt := h_fw_dist_lt)
    let f_bar_i := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (h_i := by omega) (f := f_i) (h_within_radius := h_dist_curr_lt)
    let f_bar_i_plus_steps := UDRCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := by omega)
      f_i_plus_steps h_dist_next_lt
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := i)
      h_destIdx h_destIdx_le
      f_bar_i challenges = f_bar_i_plus_steps

omit [CharP L 2] in
/--
Farness implies non-compliance. If `f_i` is far from its code `C_i`, it cannot be
compliant. This follows directly from the contrapositive of
`fiberwise_dist_lt_imp_dist_lt`.
-/
lemma farness_implies_non_compliance (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ) [NeZero steps]
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx)
  (challenges : Fin steps → L)
  (h_far : 2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    ≥ (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) : ℕ∞)) :
  ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f_i := f_i) (f_i_plus_steps := f_i_plus_steps) (challenges := challenges) := by -- We use our key theorem that "fiber-wise close" implies "Hamming close".
  intro h_compliant
  rcases h_compliant with ⟨h_fw_dist_lt, _, _⟩
  have h_close := UDRClose_of_fiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (destIdx := destIdx)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) (h_fw_dist_lt := h_fw_dist_lt)
  have h_not_far := LT.lt.not_ge h_close
  exact h_not_far h_far

/-- **Fold error containment**: Two words achieve `fold error containment` for a specific tuple of challenges if folding them does not
introduce new errors outside of their fiberwise disagreement set. -/
def fold_error_containment (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f f_bar : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (r_challenges : Fin steps → L) :=
    let fiberwise_Δ_set := fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (f := f) (g := f_bar)
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := i)
      h_destIdx h_destIdx_le (f := f) (r_challenges := r_challenges)
    let folded_f_bar := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := i)
      h_destIdx h_destIdx_le (f := f_bar) (r_challenges := r_challenges)
    let folded_Δ_set := disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := by omega) (f := folded_f) (g := folded_f_bar)
    folded_Δ_set ⊆ fiberwise_Δ_set

/-! **Lemma 4.18.** For each `i ∈ {0, steps, ..., ℓ-steps}`, if `f⁽ⁱ⁾` is `UDR-close`, then, for each tuple of folding challenges `(rᵢ', ..., r_{i+steps-1}') ∈ L^steps`, we have that `fold error containment` holds.
-- * **Main Idea of Proof:** Proceeds by contraposition. If `y ∉ Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾)`, then the restrictions of `f⁽ⁱ⁾` and `f̄⁽ⁱ⁾` to the fiber over `y` are identical. By Definition 4.8, this implies their folded values at `y` are also identical.
-- * **Intuition**: Because folding is local (Def 4.8), if `f⁽ⁱ⁾` and `f̄⁽ⁱ⁾` agree completely on the fiber above a point `y`, their folded values at `y` must also agree.
-- * **Consequence**: If `f⁽ⁱ⁾` is close to `f̄⁽ⁱ⁾`, then `fold(f⁽ⁱ⁾)` must be close to `fold(f̄⁽ⁱ⁾)`.
-/
lemma fold_error_containment_of_UDRClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ) [NeZero steps]
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (challenges : Fin steps → L)
  (h_UDRClose : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega) (f := f_i)) :
  let f_bar := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega) (f := f_i) (h_within_radius := h_UDRClose)
  fold_error_containment 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) (f_bar := f_bar) (r_challenges := challenges) := by
-- 1. Unfold definitions
  unfold fold_error_containment disagreementSet fiberwiseDisagreementSet

  set f_bar := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega) (f := f_i) (h_within_radius := h_UDRClose)

  -- 2. Start the subset proof
  simp only
  intro y -- convert subset relation to membership implication of y
  -- ⊢ **y in folded disagreement set → y in fiberwise disagreement set**
  intro hy_in_folded_disagreement -- ⊢ **y in fiberwise disagreement set**

  -- 3. Proof by contradiction (or contraposition logic)
  -- The hypothesis says: folded_f(y) ≠ folded_f_bar(y)
  simp only [ne_eq, mem_filter, mem_univ, true_and] at hy_in_folded_disagreement

  -- We want to show y ∈ fiberwiseDisagreementSet
  -- This means: ∃ x in fiber(y), f(x) ≠ f_bar(x)
  -- Let's assume the opposite: ∀ x in fiber(y), f(x) = f_bar(x)
  by_contra h_not_in_fiber_disagreement
  simp only [Fin.eta, ne_eq, Subtype.exists, mem_filter, mem_univ, true_and, not_exists, not_and,
    Decidable.not_not] at h_not_in_fiber_disagreement

  -- 4. Use Lemma 4.9 (iterated_fold_eq_matrix_form) to express the fold operation
  -- We need to show that if the fiber inputs are equal, the folded output is equal.

  let folded_f_y := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      (i := i) h_destIdx h_destIdx_le
      (f := f_i) (r_challenges := challenges) (y := y)

  let folded_f_bar_y := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      (i := i) h_destIdx h_destIdx_le
      (f := f_bar) (r_challenges := challenges) (y := y)

  -- Apply the matrix form lemma to both sides
  have h_matrix_f := iterated_fold_eq_matrix_form 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_i) (r_challenges := challenges)
  have h_matrix_f_bar := iterated_fold_eq_matrix_form 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_bar) (r_challenges := challenges)

  rw [h_matrix_f] at hy_in_folded_disagreement
  rw [h_matrix_f_bar] at hy_in_folded_disagreement

  -- 5. Show the RHS of the matrix forms are equal
  -- The RHS depends on `localized_fold_matrix_form`.
  -- This function depends on `foldMatrix` (same for both) and `fiberEvaluations`.
  -- We just need to show `fiberEvaluations` is the same for both.

  set fiberEvals_f_i := fiberEvaluations 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_i) y
  set fiberEvals_f_bar_i := fiberEvaluations 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_bar) y
  have h_fiber_evals_eq : fiberEvals_f_i = fiberEvals_f_bar_i := by
    ext k
    unfold fiberEvals_f_i fiberEvals_f_bar_i fiberEvaluations
    -- The k-th fiber point x is:
    let x := qMap_total_fiber 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le y k

    -- We need to show f_i(x) = f_bar(x).
    -- This follows from our contradiction hypothesis `h_not_in_fiber_disagreement`.
    apply h_not_in_fiber_disagreement x

    -- We must prove x is actually in the fiber of y (which is true by construction/definition)
    -- Use the lemma `generates_quotient_point_if_is_fiber_of_y` or similar
    let res := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (x := x) (y := y) (hx_is_fiber := by use k)
    exact res.symm

  -- 6. Final Contradiction
  -- Since the fiber evaluations are equal, the matrix products must be equal.
  -- localized_fold_matrix_form is just a function of these evaluations.
  have h_folded_eq : localized_fold_matrix_form 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_i) (r_challenges := challenges) y =
                     localized_fold_matrix_form 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_bar) (r_challenges := challenges) y := by
    unfold localized_fold_matrix_form
    simp only
    unfold fiberEvals_f_i fiberEvals_f_bar_i at h_fiber_evals_eq
    rw [h_fiber_evals_eq]

  -- Contradiction: We proved they are equal, but hypothesis says they are unequal.
  exact hy_in_folded_disagreement h_folded_eq

open Classical in
/-- **Definition 4.19** Bad event for folding : This event captures two scenarios where the
random folding challenges undermine the protocol's soundness checks.
For `i ∈ {0, ..., ℓ - steps}`,
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ₊steps / 2` (fiberwise close):
  `Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ(fold(f⁽ⁱ⁾, rᵢ', ..., r_{i+steps-1}'), fold(f̄⁽ⁱ⁾, rᵢ', ..., r_{i+steps-1}'))`, i.e. fiberwiseDisagreementSet ⊄ foldedDisagreementSet
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ dᵢ₊steps / 2`  (fiberwise far):
  `d(fold(f⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'), C⁽ⁱ⁺steps⁾) < dᵢ₊steps / 2`, i.e. foldedUDRClose -/
def foldingBadEvent (i : Fin r) {destIdx : Fin r} (steps : ℕ) (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ) [NeZero steps]
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (r_challenges : Fin steps → L) : Prop :=

  let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_i) (r_challenges := r_challenges)

  if h_is_close : (fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_i)) then
    -- Case 1 : The oracle `f_i` is fiber-wise "close" to the code.
    -- The bad event is when folding causes disagreements to vanish, violating Lemma 4.18.
    -- This happens if the random challenges are unlucky.

    let f_bar_i := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i (f := f_i) (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f_i h_is_close)

    let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f_bar_i) (r_challenges := r_challenges)

    -- The Bad Condition: FiberDisagreements ⊈ FoldedDisagreements
    ¬ (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le (f := f_i) (g := f_bar_i) ⊆
       disagreementSet 𝔽q β (i := destIdx) (h_i := by omega) (f := folded_f_i) (g := folded_f_bar_i))

  else
    -- Case 2 : The oracle `f_i` is fiber-wise "far" from the code.
    -- Folding a "far" function should result in another "far" function.
    -- The bad event is when folding makes this far function appear "close" to the code.
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
      (h_i := by omega) (f := folded_f_i)

end SoundnessTools

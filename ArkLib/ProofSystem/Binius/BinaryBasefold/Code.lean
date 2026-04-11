/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open Code ReedSolomon BerlekampWelch ProbabilityTheory

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
  Submodule L (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i → L) :=
  let domain : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  ReedSolomon.code (domain := domain) (deg := 2^(ℓ - i.val))

lemma exists_BBF_poly_of_codeword (i : Fin r)
  (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  ∃ P : L⦃<2^(ℓ-i)⦄[X],
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P) = u := by
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
    : Set (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i → L))‖₀

lemma BBF_CodeDistance_eq (i : Fin r) (h_i : i ≤ ℓ) :
  BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    = 2^(ℓ + 𝓡 - i.val) - 2^(ℓ - i.val) + 1 := by
  sorry

/-- Disagreement set Δ : The set of points where two functions disagree.
For functions f^(i) and g^(i), this is {y ∈ S^(i) | f^(i)(y) ≠ g^(i)(y)}. -/
def disagreementSet (i : Fin r)
  {destIdx : Fin r} (h_destIdx : destIdx = i.val)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) destIdx) :=
  have h_destIdx_eq_i : destIdx = i := Fin.ext h_destIdx
  {(y : (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) destIdx) |
    f (cast (by subst h_destIdx_eq_i; rfl) y) ≠ g (cast (by subst h_destIdx_eq_i; rfl) y)}

/-- Fiber-wise disagreement set Δ^(i) : The set of points y ∈ S^(i+ϑ) for which
functions f^(i) and g^(i) are not identical when restricted to the entire fiber
of points in S⁽ⁱ⁾ that maps to y. -/
def fiberwiseDisagreementSet (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) destIdx) :=
  -- The set of points `y ∈ S^{i+steps}` whose fiber contains a disagreement.
  {y | ∃ k : Fin (2 ^ steps),
    f (qMap_total_fiber 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le y k) ≠
      g (qMap_total_fiber 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le y k)}

lemma fiberwiseDisagreementSet_congr_sourceDomain_index (sourceIdx₁ sourceIdx₂ : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
  (h_destIdx : destIdx = sourceIdx₁.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) sourceIdx₁) :
  -- have h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂ := Fin.ext h_sourceIdx_eq_sourceIdx₂
  let Δ_fiber₁ := fiberwiseDisagreementSet 𝔽q β sourceIdx₁ steps h_destIdx h_destIdx_le f g
  let Δ_fiber₂ := fiberwiseDisagreementSet 𝔽q β sourceIdx₂ steps (by omega) h_destIdx_le (fun x => f (cast (by subst h_sourceIdx_eq; rfl) x)) (fun x => g (cast (by subst h_sourceIdx_eq; rfl) x))
  Δ_fiber₁ = Δ_fiber₂ := by
  sorry

/-- When `steps = 0`, the fiberwise disagreement set (projecting to `S^{i+0} = S^i`)
equals the ordinary pointwise disagreement set.
Both sides are stated with `destIdx := i` so they share the same `Finset` type. -/
@[simp]
lemma fiberwiseDisagreementSet_steps_zero_eq_disagreementSet
    (i destIdx : Fin r) (h_destIdx : destIdx = i.val + 0) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    fiberwiseDisagreementSet 𝔽q β i (steps := 0) (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f g =
    disagreementSet 𝔽q β (i := i) (destIdx := destIdx) (h_destIdx := h_destIdx) f g := by
  sorry

def pair_fiberwiseDistance (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : ℕ :=
    (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g).card

/-- Fiber-wise distance d^(i) : The minimum size of the fiber-wise disagreement set
between f^(i) and any codeword in C^(i). -/
def fiberwiseDistance (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
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
def fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx): ℕ∞)

def pair_fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
    2 * pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps
      h_destIdx h_destIdx_le (f := f) (g := g) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx): ℕ∞)

/-- Hamming UDR-closeness : f is close to C in Hamming distance if `2 * d(f, C) < d_i` -/
def UDRClose (i : Fin r) (h_i : i ≤ ℓ)
    (f : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i → L) : Prop :=
    2 * Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

def pair_UDRClose (i : Fin r) (h_i : i ≤ ℓ)
    (f g : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i → L) : Prop :=
  2 * Δ₀(f, g) < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

/-- Congruence lemma for `UDRClose`: transport along a `Fin r` equality.
Given two `Fin r` indices with the same value and `HEq` functions, `UDRClose` transfers. -/
lemma UDRClose_of_fin_eq {i j : Fin r} (hij : i = j)
    {hi : ↑i ≤ ℓ} {hj : ↑j ≤ ℓ}
    {f : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i → L}
    {g : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j → L}
    (hfg : HEq f g) (h : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hi f) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j hj g := by
  subst hij
  exact eq_of_heq hfg ▸ h

/-- When `steps = 0`, `pair_fiberwiseDistance` equals the Hamming distance. -/
@[simp]
lemma pair_fiberwiseDistance_steps_zero_eq_hammingDist
    (i : Fin r) (h_i_le : i ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := i) (steps := 0) (h_destIdx := by omega) (h_destIdx_le := by omega) (f := f) (g := g) = hammingDist f g := by
  rw [pair_fiberwiseDistance, fiberwiseDisagreementSet_steps_zero_eq_disagreementSet 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := i) (h_destIdx := by omega) (h_destIdx_le := by omega) f g]
  simp only [disagreementSet, cast_eq, ne_eq, card_filter, ite_not, hammingDist]

/-- When `steps = 0`, fiberwise closeness coincides with UDR closeness. -/
@[simp]
lemma fiberwiseClose_steps_zero_iff_UDRClose
    (i destIdx : Fin r) (h_destIdx : destIdx = i.val + 0) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (steps := 0) (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f ↔
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f := by
  have h_destIdx_eq_i : destIdx = i := Fin.ext h_destIdx
  subst h_destIdx_eq_i
  have h_dist_eq :
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
        (steps := 0) (destIdx := destIdx) (h_destIdx := by simp)
        (h_destIdx_le := by omega) (f := f) : ℕ∞) =
        Δ₀(f, (↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
          Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))) := by
    let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    let S : Set ℕ := (fun (g : C_i) => hammingDist f g) '' Set.univ
    let SENat : Set ℕ∞ := (fun (g : C_i) => (hammingDist f g : ℕ∞)) '' Set.univ
    have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
      rw [ENat.coe_sInf (hs := hS_nonempty)]
      simp only [SENat, Set.image_univ, sInf_range]
      simp only [S, Set.image_univ, iInf_range]
    have h_distFromCode_eq_sInf :
        Δ₀(f, (↑C_i :
          Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))) =
        sInf SENat := by
      apply le_antisymm
      · simp only [Code.distFromCode]
        apply sInf_le_sInf
        intro a ha
        rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
        exact ⟨g, g.property, le_refl _⟩
      · simp only [Code.distFromCode]
        apply le_sInf
        intro d hd
        rcases hd with ⟨v, hv_mem, h_dist_v_le_d⟩
        have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist f v) := by
          apply sInf_le
          rw [Set.mem_image]
          exact ⟨⟨v, hv_mem⟩, Set.mem_univ _, rfl⟩
        exact h_sInf_le_dist_v.trans h_dist_v_le_d
    unfold fiberwiseDistance
    simp only [pair_fiberwiseDistance_steps_zero_eq_hammingDist]
    rw [h_coe_sinfS_eq_sinfSENat, ← h_distFromCode_eq_sInf]
  unfold fiberwiseClose UDRClose
  rw [h_dist_eq]

lemma fiberwiseClose_congr_sourceDomain_index (sourceIdx₁ sourceIdx₂ : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
  (h_destIdx : destIdx = sourceIdx₁.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) sourceIdx₁) :
  -- have h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂ := Fin.ext h_sourceIdx_eq_sourceIdx₂
  let Δ_fiber₁ := fiberwiseClose 𝔽q β sourceIdx₁ steps h_destIdx h_destIdx_le f
  let Δ_fiber₂ := fiberwiseClose 𝔽q β sourceIdx₂ steps (by omega) h_destIdx_le (fun x => f (cast (by subst h_sourceIdx_eq; rfl) x))
  Δ_fiber₁ = Δ_fiber₂ := by
  subst h_sourceIdx_eq
  rfl

section ConstantFunctions

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
  unfold UDRClose
  have h_zero :
      Code.distFromCode (fun _ => c)
        ((↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
          Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) = 0 := by
    exact Code.distFromCode_of_mem
      (C := ((↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
        Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)))
      (u := fun _ => c)
      (constFunc_mem_BBFCode 𝔽q β h_i c)
  simp [h_zero]
  rw [BBF_CodeDistance_eq 𝔽q β (i := i) (h_i := h_i)]
  omega

end ConstantFunctions
lemma UDRClose_iff_within_UDR_radius (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f ↔
    Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≤
      uniqueDecodingRadius (ι := (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
        (F := L) (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  unfold UDRClose
  let card_Sᵢ := AdditiveNTT.Comp.sDomain_card (𝔽q := 𝔽q) (β := β) h_ℓ_add_R_rate (i := i) (h_i := Sdomain_bound (by omega))
  conv_rhs =>
    unfold BBF_Code;
    rw [ReedSolomonCode.uniqueDecodingRadius_RS_eq' (h := by
      rw [card_Sᵢ, hF₂.out]; apply Nat.pow_le_pow_right (hx := by omega); omega
    )];
  simp_rw [card_Sᵢ, hF₂.out,
    BBF_CodeDistance_eq 𝔽q β (i := i) (h_i := by omega)]
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

open Classical in
lemma UDRCodeword_eq_of_close
    (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h₁ h₂ : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h₁ =
      UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h₂ := by
  sorry

lemma UDRCodeword_constFunc_eq_self (i : Fin r) (h_i : i ≤ ℓ) (c : L) :
  UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_i (f := fun _ => c)
    (h_within_radius := by apply constFunc_UDRClose) = fun _ => c := by
  sorry

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

lemma dist_to_UDRCodeword_le_uniqueDecodingRadius (i : Fin r) (h_i : i ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  Δ₀(f, UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_within_radius) ≤
    uniqueDecodingRadius (ι := (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
      (F := L) (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  ) -- res : ∃! v, v ∈ ↑(BBF_Code 𝔽q β i) ∧ Δ₀(f, v) ≤ uniqueDecodingRadius ↑(BBF_Code 𝔽q β i)
  let res := (Classical.choose_spec h_ExistsUnique).1
  simp only [SetLike.mem_coe, and_imp] at res
  let h_close := res.2
  unfold UDRCodeword
  simp only [SetLike.mem_coe, and_imp, ge_iff_le]
  exact h_close

/-- Computational version of `UDRCodeword`, where we use the Berlekamp-Welch decoder to extract
the closest codeword within the unique decoding radius of a function `f` -/
def extractUDRCodeword
  (i : Fin r) (h_i : i ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i)
   := by
  sorry
  /- Set up Berlekamp-Welch parameters
  set domain_size := Fintype.card (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
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
  let domain_to_fin : (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) i ≃ Fin domain_size := by
    haveI : Fintype (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := inferInstance
    simpa [domain_size] using
      (Fintype.equivFin (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [AdditiveNTT.Comp.sDomain_card (𝔽q := 𝔽q) (β := β) h_ℓ_add_R_rate (i := i) (h_i := Sdomain_bound h_i)]
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
      (fun (x : AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)) ↦ p.eval (↑x)) = g_closest := by
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
          have hS_card_eq_domain_size := AdditiveNTT.Comp.sDomain_card (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := i) (h_i := Sdomain_bound (by omega))
          simp only [domain_size, k]; simp_rw [hS_card_eq_domain_size, hF₂.out]
          unfold UDRClose at h_within_radius
          rw [BBF_CodeDistance_eq 𝔽q β
            (h_i := by omega)] at h_within_radius
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
        rw [AdditiveNTT.Comp.sDomain_card (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (h_i := Sdomain_bound (by omega)), hF₂.out]
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
          ext j; simp only [Function.comp_apply, ωs]
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
  -/

/-! `Δ₀(f, g) ≤ pair_fiberwiseDistance(f, g) * 2 ^ steps` -/
lemma hammingDist_le_fiberwiseDistance_mul_two_pow_steps (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  [NeZero steps] (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Δ₀(f, g) ≤ (pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      steps h_destIdx h_destIdx_le (f := f) (g := g)) * 2 ^ steps := by
  sorry

/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, g⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, g⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
lemma pairUDRClose_of_pairFiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps]
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_dist_lt : pair_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f g) :
    pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (by omega) (f := f)
      (g := g) := by
  sorry

lemma exists_fiberwiseClosestCodeword (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps]
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    let S_i := AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃ (g : S_i → L), g ∈ C_i ∧
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g) := by
  simp only [SetLike.mem_coe]
  set S_i := AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  set C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  -- Let `S` be the set of all possible fiber-wise disagreement sizes.
  let S := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (g := g)).card) '' Set.univ
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

/-! if `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
@[simp]
theorem UDRClose_of_fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ) [NeZero steps]
  (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
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

/-! This expands `exists_fiberwiseClosestCodeword` to the case `f` is fiberwise-close to `C_i`. -/
lemma exists_unique_fiberwiseClosestCodeword_within_UDR (i : Fin r) {destIdx : Fin r}
    (steps : ℕ) [NeZero steps] (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
    let S_i := AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃! (g : S_i → L), (g ∈ C_i) ∧
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g)) ∧
      (g = UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f
        (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f
        h_fw_close))
      := by
  sorry

/-- **Lemma: Single Step BBF_Code membership preservation**
It establishes that folding a codeword from the i-th code produces a codeword in the (i+1)-th code.
This relies on **Lemma 4.14** that 1-step folding advances the evaluation polynomial. -/
lemma fold_preserves_BBF_Code_membership (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) (r_chal : L) :
    (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_destIdx h_destIdx_le
      (f := f) (r_chal := r_chal)) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  sorry

/-- **Lemma: Iterated BBF_Code membership preservation (Induction)**
If `f` is in BBF_Code `C^{(i)}`, then `iterated_fold f r` is in BBF_Code `C^{(i+steps)}`.
NOTE: we can potentially specifify the structure of the folded polynomial. -/
lemma iterated_fold_preserves_BBF_Code_membership (i : Fin r) {destIdx : Fin r} (steps : ℕ)
  (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
  (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (r_challenges : Fin steps → L) :
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (f := f) (r_challenges := r_challenges)) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  sorry

end SoundnessTools
end Binius.BinaryBasefold

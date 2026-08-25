/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/

import ArkLib.Data.CodingTheory.Basic.BlockRelDistance
import ArkLib.Data.CodingTheory.ProximityGap.Folding
import ArkLib.Data.CodingTheory.ProximityGap.Folding.FoldingContext
import ArkLib.Data.Domain.CosetFftDomain.Pullback

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Polynomial Domain
open CosetFftDomain CosetFftDomainClass
open BlockRelDistance

variable {F : Type} [Field F] [DecidableEq F]
variable {n k d : ℕ}
variable {ω : SmoothCosetFftDomain n F}
variable {f : Word F (Fin (2 ^ n))}

/-!
  This file contains a proof of Theorem 4.20 from [ACFY24] (WIP for now).

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
-/

open FoldingContext in
/-- The block distance of foldings of two words does not exceed
  the block distance of the original words.

  This is a part of the proof of the claim 4.22 of [ACFY24]. -/
lemma folding_contracts_block_distance [FoldingContextMiddle k n]
  {α : F} {u : Word F (Fin (2 ^ n))} :
  Δ𞁒(k - 1, ω.subdomain 1, foldWord ω u 1 α, foldWord ω f 1 α) ≤
    Δ𞁒(k , ω, u, f) := by
  simp only [blockDistance, card_disagreementSet', card_toFinset,
    FoldingContext.n_sub_1_sub_k_sub_1_eq_n_sub_k, Fintype.card_fin]
  rw [Nat.sub_le_sub_iff_left (by simp)]
  exact Finset.card_le_card <| fun x hx ↦ by
    simp_all only [complDisagreementSet_def', mem_filter]
    exact And.intro
      (by aesop (add safe (by grind))) <| fun i hi ↦ by
      rw [foldWord_k_1, foldWord_k_1]
      extract_lets y j j'
      have : 2 ^ k = 2 * 2 ^ (k - 1) := by grind [←pow_succ']
      have hj : j ∈ blockIdx ω k x := by
        aesop
          (add simp [mem_blockIdx_iff_mem_block, pow_mul])
          (add unsafe (by rw [←CosetFftDomainClass.mem_toFinset_iff_mem]))
      have hj' : j' ∈ blockIdx ω k x := by
        aesop
          (add simp [mem_blockIdx_iff_mem_block, pow_mul])
          (add unsafe (by rw [←CosetFftDomainClass.mem_toFinset_iff_mem]))
      rw [hx.2 _ hj, hx.2 _ hj']

/-- The block relative distance of foldings of two words does not exceed
  the block relative distance of the original words.

  This is a part of the proof of the claim 4.22 of [ACFY24]. -/
lemma folding_contracts_block_rel_distance [FoldingContextMiddle k n]
  {α : F} {u : Word F (Fin (2 ^ n))} :
  δ𞁒(k - 1, ω.subdomain 1, foldWord ω u 1 α, foldWord ω f 1 α) ≤
    δ𞁒(k , ω, u, f) := by
  aesop
    (add simp [blockRelDistance, FoldingContext.n_sub_1_sub_k_sub_1_eq_n_sub_k])
    (add unsafe folding_contracts_block_distance)
    (add safe (by field_simp))

open FoldingContext in
/-- If a word `u` belongs to a block relative distance ball
  then its folding belongs to a "folded" block relative distance ball too.

  This is the claim 4.22 from [ACFY24] with unfolded definition `⊆`.
-/
lemma folding_block_rel_ball {d : ℕ} [FoldingContext k d n]
  {α : F} {δ : ℝ≥0} {u : Word F (Fin (2 ^ n))}
  (hu : u ∈ Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), k, ω, f, δ)) :
  foldWord ω u 1 α ∈
    Λ𞁒(code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)),
       k - 1, ω.subdomain 1,
       foldWord ω f 1 α, δ) := by
  simp_all only [Word, blockRelDistanceBall, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · have := FoldingContext.oneStep
    exact foldWord_mem_code_of_mem_code hu.1
  · exact le_trans
      (NNRat.cast_le.2 <| folding_contracts_block_rel_distance)
      (by aesop)

/-- The image of a block relative distance ball under the folding map
  is contained in the "folded" block relative distance ball.

  This is the claim 4.22 from [ACFY24].
-/
theorem folding_preserves_block_balls {d : ℕ} [FoldingContext k d n] {α : F} {δ : ℝ≥0} :
  Set.image
    (fun u ↦ foldWord ω u 1 α)
    (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), k, ω, f, δ)) ⊆
      Λ𞁒(code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)),
         k - 1, ω.subdomain 1, foldWord ω f 1 α, δ) := fun x hx ↦ by
  aesop (add unsafe folding_block_rel_ball)

open Domain Pullback

private def foldingBlockAgreementAux
  (k : ℕ)
  (ω : SmoothCosetFftDomain n F)
  (α : F) (u0 u1 v : Word F (Fin (2 ^ (n - 1)))) :
  Finset ((Fin (2 ^ (n - 1))) × (Fin (2 ^ (n - k)))) :=
  pullback ω 1 k <|
    complDisagreementSet (k - 1) (ω.subdomain 1) (u0 + α • u1) v

open FoldingContext in
lemma card_foldingBlockAgreementAux_eq'
  [FoldingContextMiddle k n]
  {α : F} {u0 u1 v : Word F (Fin (2 ^ (n - 1)))} :
  Finset.card (foldingBlockAgreementAux k ω α u0 u1 v) =
    Finset.card (complDisagreementSet (k - 1) (ω.subdomain 1) (u0 + α • u1) v) * 2 ^ (k - 1) := by
  have :
    complDisagreementSet (k - 1) (ω.subdomain 1) (u0 + α • u1) v ⊆
      (ω.subdomain k).toFinset := 
        complDisagreementSet_sub_subdomain.trans <| fun x hx ↦ by
          aesop (add safe (by grind))
  aesop 
    (add simp foldingBlockAgreementAux)
    (add safe [(by rw [card_pullback_eq_mul_card_pullback₂,
                       card_pullback₂_eq, mul_comm]), 
               (by grind)])

lemma card_foldingBlockAgreementAux_eq''
  [FoldingContextMiddle k n]
  {α : F} {u0 u1 v : Word F (Fin (2 ^ (n - 1)))} :
  Finset.card (foldingBlockAgreementAux k ω α u0 u1 v) =
    (2 ^ (n - k) - Δ𞁒(k - 1, ω.subdomain 1, u0 + α • u1, v)) * 2 ^ (k - 1) := by
  aesop 
    (add simp [card_foldingBlockAgreementAux_eq',
               card_complDisagreementSet, 
               FoldingContext.n_sub_1_sub_k_sub_1_eq_n_sub_k])

private def foldingBlockAgreement
  (k : ℕ) (ω : SmoothCosetFftDomain n F)
  (α : F) (u0 u1 v : Word F (Fin (2 ^ (n - 1)))) :
  Finset (Fin (2 ^ (n - 1))) :=
  pullback₁ ω 1 k <|
    complDisagreementSet (k - 1) (ω.subdomain 1) (u0 + α • u1) v

lemma card_foldingBlockAgreement
  {α : F} {u0 u1 v : Word F (Fin (2 ^ (n - 1)))} :
  Finset.card (foldingBlockAgreement k ω α u0 u1 v) =
    Finset.card (foldingBlockAgreementAux k ω α u0 u1 v) := by
  rw [foldingBlockAgreement, 
      foldingBlockAgreementAux,
      card_pullback_eq_card_pullback₁]

lemma card_foldingBlockAgreement_ge [FoldingContextMiddle k n]
  {α : F} {u0 u1 v : Word F (Fin (2 ^ (n - 1)))} :
  (Finset.card (foldingBlockAgreement k ω α u0 u1 v) : ℝ≥0) ≥
    2 ^ (n - 1) * (1 - δ𞁒(k - 1, ω.subdomain 1, u0 + α • u1, v)) := by
  rw [card_foldingBlockAgreement, card_foldingBlockAgreementAux_eq'']
  have : Δ𞁒(k - 1, CosetFftDomain.subdomain ω 1, u0 + α • u1, v) ≤ (2 : ℝ≥0) ^ (n - k) := by
    norm_cast
    grind [blockDistance_le]
  have : k - 1 + (n - k) = n - 1 := by grind
  simp [←NNReal.coe_le_coe]
  aesop
    (add simp [blockRelDistance])
    (add safe [(by grind), (by field_simp), le_of_eq])

open FoldingContext in
lemma foldingBlockAgreement_is_agreement [FoldingContextMiddle k n]
  {α : F} {u0 u1 v : Word F (Fin (2 ^ (n - 1)))}
  {i : Fin (2 ^ (n - 1))} (hi : i ∈ foldingBlockAgreement k ω α u0 u1 v) :
  u0 i + α * u1 i = v i := by
  aesop 
    (add safe (by grind [mem_pullback₁])) 
    (add simp [foldingBlockAgreement,   
               complDisagreementSet_def',
               mem_blockIdx_iff_mem_block])

lemma agreement_on_z_of_u0_u1_polynomials [NeZero n]
  {u₀ u₁ : Polynomial F}
  (z : Finset (Fin (2 ^ (n - 1))))
  (hu₀ : ∀ i ∈ z,
    let x : ω := CosetFftDomain.twoNthRoot (i := 1)
        ⟨ω.subdomain 1 i, by simp⟩
    let j := ω.log x
    let j' := ω.log ⟨-x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩
    (f j + f j') / 2 = u₀.eval (ω.subdomain 1 i))
  (hu₁ : ∀ i ∈ z,
    let x : ω := CosetFftDomain.twoNthRoot (i := 1)
        ⟨ω.subdomain 1 i, by simp⟩
    let j := ω.log x
    let j' := ω.log ⟨-x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩
    (f j - f j') / (2 * ω j) = u₁.eval (ω.subdomain 1 i))
  {j : Fin (2 ^ n)}
  (hj : ω j ^ 2 ∈ (ω.subdomain 1) '' z) :
  f j =
    (u₀.comp (Polynomial.X ^ 2) + Polynomial.X * u₁.comp (Polynomial.X ^ 2)).eval
      (ω j) := by
  obtain ⟨l, hlz, hl⟩ := hj
  have := foldWord_k_1 (domain := ω) (f := f) (i := l) (α := ω j)
  simp only [eval_add, eval_comp, eval_pow, eval_X, ←hl, ←hu₀ _ hlz, eval_mul, ←hu₁ _ hlz,
    log_right_inverse']
  simp_all [foldWord_k_1_eval_domain]

def foldingBlockAgreementᵣ
  (k : ℕ) (ω : SmoothCosetFftDomain n F)
  (α : F) (u0 u1 v : Word F (Fin (2 ^ (n - 1)))) :
  Finset (Fin (2 ^ (n - k))) :=
  pullback₂ ω 1 k <|
    complDisagreementSet (k - 1) (ω.subdomain 1) (u0 + α • u1) v

open FoldingContext in
lemma mem_foldingBlockAgreementᵣ
  {u : Fin (2 ^ (n - k))} {α : F}
  [FoldingContextMiddle k n]
  {u0 u1 v : Word F (Fin (2 ^ (n - 1)))} :
  u ∈ foldingBlockAgreementᵣ k ω α u0 u1 v ↔
    ∀ j ∈ blockIdx (ω.subdomain 1) (k - 1) (ω.subdomain k u),
        u0 j + α * (u1 j) = v j := by
  rw [foldingBlockAgreementᵣ, mem_pullback₂ (by grind) (by grind), complDisagreementSet_def']
  simp_all only [mem_blockIdx_iff_mem_block, mem_block, mem_self, true_and, Word, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, mem_filter, CosetFftDomainClass.mem_toFinset_iff_mem,
    and_iff_right_iff_imp]
  rw [mem_subdomain_comp_iff_mem (by grind), show 1 + (k - 1) = k by grind]
  aesop (add safe (by grind))

lemma mem_foldingBlockAgreementᵣ_of_mem_foldingBlockAgreement
  {j : Fin (2 ^ n)} {α : F}
  [FoldingContextMiddle k n]
  {u0 u1 v : Word F (Fin (2 ^ (n - 1)))} :
  ω j ^ 2 ∈ ω.subdomain 1 '' foldingBlockAgreement k ω α u0 u1 v ↔
    ω j ^ 2 ^ k ∈ ω.subdomain k '' foldingBlockAgreementᵣ k ω α u0 u1 v := by
  unfold foldingBlockAgreement foldingBlockAgreementᵣ
  rw [mem_pullback₁_iff_mem_pullback₂_l_1] <;> grind

lemma card_foldingBlockAgreementᵣ'
  [FoldingContextMiddle k n]
  {α : F} {u0 u1 v : Word F (Fin (2 ^ (n - 1)))} :
  Finset.card (foldingBlockAgreementᵣ k ω α u0 u1 v) =
    Finset.card (complDisagreementSet (k - 1) (ω.subdomain 1) (u0 + α • u1) v) := by
  rw [foldingBlockAgreementᵣ, card_pullback₂_eq (by grind) (by grind)] 
  intro x hx
  replace hx := complDisagreementSet_sub_subdomain hx
  aesop (add safe (by grind))

lemma card_foldingBlockAgreement_foldingBlockAgreementᵣ
  [FoldingContextMiddle k n]
  {α : F} {u0 u1 v : Word F (Fin (2 ^ (n - 1)))} :
  Finset.card (foldingBlockAgreement k ω α u0 u1 v) =
    2 ^ (k - 1) * Finset.card (foldingBlockAgreementᵣ k ω α u0 u1 v) := by
  rw [card_foldingBlockAgreement,
      card_foldingBlockAgreementAux_eq',
      card_foldingBlockAgreementᵣ']
  ac_nf

lemma card_foldingBlockAgreement_foldingBlockAgreementᵣ_le
  (δ : ℝ≥0)
  [FoldingContextMiddle k n]
  {α : F} {u0 u1 v : Word F (Fin (2 ^ (n - 1)))}
  (h : 2 ^ (n - 1) * (1 - δ) ≤ Finset.card (foldingBlockAgreement k ω α u0 u1 v)) :
  2 ^ (n - k) * (1 - δ) ≤
    Finset.card (foldingBlockAgreementᵣ k ω α u0 u1 v) := by
  rw [card_foldingBlockAgreement_foldingBlockAgreementᵣ] at h
  conv_lhs =>
    rw [←FoldingContext.n_sub_1_sub_k_sub_1_eq_n_sub_k,
        show ((2 : ℝ≥0) ^ (n - 1 - (k - 1))) = 2 ^ (n - 1) / 2 ^ (k - 1) by 
          aesop (add safe [(by field_simp), (by grind), (by rw [←pow_add])])]
  aesop (add safe [(by field_simp), (by norm_cast)])

lemma distance_of_u0_u1_polynomials [NeZero n]
  {u₀ u₁ : Polynomial F}
  (z : Finset (Fin (2 ^ (n - k))))
  (hz : ∀ j, ω j ^ 2 ^ k ∈ ω.subdomain k '' z →
      f j = u₀.eval (ω j ^ 2) + (ω j) * u₁.eval (ω j ^ 2)) :
  Δ𞁒(k, ω, f,
      evalOnPoints ω
        (u₀.comp (Polynomial.X ^ 2) + Polynomial.X * u₁.comp (Polynomial.X ^ 2))) ≤
    2 ^ (n - k) - Finset.card z := by
  simp only [blockDistance]
  rw [card_disagreementSet']
  simp only [card_toFinset, Fintype.card_fin]
  rw [Nat.sub_le_sub_iff_left (by {
    conv_rhs => rw [show 2 ^ (n - k) = Finset.card (Finset.univ (α := Fin (2 ^ (n - k)))) by simp]
    exact Finset.card_le_card (by simp)
  })]
  exact Finset.card_le_card_of_injOn
    (fun x ↦ ω.subdomain k x)
    (fun x hx ↦ by
      aesop (add simp [complDisagreementSet_def', mem_blockIdx_iff_mem_block, evalOnPoints]))
    (fun _ _ _ _ hab ↦ CosetFftDomainClass.injective _ hab)

open FoldingContext in
lemma mem_ball_of_u0_u1_polynomials [FoldingContext k d n]
  {δ : ℝ≥0} (hδ1 : δ < 1)
  {u₀ u₁ : Polynomial F}
  (hu₀_deg : u₀.degree < 2 ^ (d - 1))
  (hu₁_deg : u₁.degree < 2 ^ (d - 1))
  (z : Finset (Fin (2 ^ (n - k))))
  (hz_card : (2 ^ (n - k) * (1 - δ)) ≤ z.card)
  (hz : ∀ j, ω j ^ 2 ^ k ∈ ω.subdomain k '' z →
      f j = u₀.eval (ω j ^ 2) + (ω j) * u₁.eval (ω j ^ 2)) :
    evalOnPoints ω
      (u₀.comp (Polynomial.X ^ 2) + Polynomial.X * u₁.comp (Polynomial.X ^ 2)) ∈
      Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), k, ω, f, δ) := by
  simp only [mem_blockRelDistanceBall, SetLike.mem_coe]
  constructor
  · exact
      evalOnPoints_mem_code_of_natDegree_lt <| lt_of_le_of_lt (natDegree_add_le _ _) <| by
        simp only [natDegree_comp, natDegree_pow, natDegree_X, mul_one, sup_lt_iff]
        have hpow : 2 ^ d = 2 ^ (d - 1) * 2 := by
          conv_rhs =>
            rhs
            rw [show 2 = 2 ^ 1 by simp]
          rw [←pow_add]
          grind
        constructor
        · rw [hpow, Nat.mul_lt_mul_right (by simp)]
          by_cases hu₀ : u₀ = 0 <;>
            aesop (add simp [Polynomial.natDegree_lt_iff_degree_lt])
        · exact lt_of_le_of_lt Polynomial.natDegree_mul_le <| by
            simp only [natDegree_X, natDegree_comp, natDegree_pow, mul_one]
            have : 1 + u₁.natDegree * 2 ≠ 2 ^ d := by aesop (add safe (by grind))
            apply swap lt_of_le_of_ne this
            rw [Nat.le_iff_lt_add_one, add_comm, Nat.add_lt_add_iff_right,
                hpow, Nat.mul_lt_mul_right (by simp)]
            by_cases hu₁ : u₁ = 0 <;>
              aesop (add simp [Polynomial.natDegree_lt_iff_degree_lt])
  · apply le_trans (b := ((2 ^ (n - k) : ℝ≥0) - Finset.card z) / (2 ^ (n - k)))
    · simp only [blockRelDistance, _root_.map_add, evalOnPoints_mul, evalOnPoints_X,
      Embedding.coeFn_mk, card_toFinset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
      NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat]
      norm_cast
      field_simp
      norm_cast
      rw [blockDistance_symm]
      convert distance_of_u0_u1_polynomials z hz
      simp
    · have hδ : 2 ^ (n - k) - Finset.card z ≤ 2 ^ (n - k) * δ := by
        norm_num
        rw [←NNReal.coe_le_coe]
        rw [←NNReal.coe_le_coe,
            NNReal.coe_mul, NNReal.coe_sub (by grind),
            mul_sub] at hz_card
        norm_num at hz_card
        push_cast
        grind
      field_simp
      exact le_trans hδ (by simp)

open CoreDefinitions in
theorem folding_reflects_balls [Fintype F]
  {ε_mca : I → ℝ}
  (hmca : IsMCAGenerator (UnivariatePowers 1) ε_mca
    (ReedSolomon.code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1))))
  (hk : 1 ≤ k) (hkd : k ≤ d) (hdn : d ≤ n)
  {δ : ℝ≥0}
  (δ_gt_0 : 0 < δ) -- this one is not used but should be.
  (δ_lt : δ <
    (1 - (LinearCode.rate (ReedSolomon.code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ d))))) :
  let δ' : I := ⟨δ, by aesop, by {
              rw [show 1 = NNReal.toReal 1 by norm_cast, ←NNReal.toReal_le]
              exact le_trans (le_of_lt δ_lt) (by simp)}⟩
  Pr_{ let α ←$ᵖ F}[
    ¬(Λ𞁒(code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)),
             k - 1, ω.subdomain 1, foldWord ω f 1 α, δ)) ⊆
      Set.image
        (fun u ↦ foldWord ω u 1 α)
        (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), k, ω, f, δ))] ≤
          ENNReal.ofReal (ε_mca δ') := by
  sorry
  have : NeZero n := ⟨by omega⟩
  simp only [IsMCAGenerator, Nat.reduceAdd] at hmca
  extract_lets δ'
  let u0 := foldWordEven ω f 
  let u1 := foldWordOdd ω f
  specialize hmca (fun j i ↦ match j with | 0 => u0 i | 1 => u1 i) δ'
  simp only [bind_pure_comp, Functor.map,
        PMF.bind_apply,
        PMF.uniformOfFintype_apply,
        comp_apply, PMF.pure_apply, eq_iff_iff, true_iff,
        mul_ite, mul_one, mul_zero, tsum_fintype] at hmca ⊢
  exact le_trans' hmca <| Finset.sum_le_sum <| fun α _ ↦ by
    split_ifs with h₁ h₂ <;> try rfl
    · simp only [Word, eq_iff_iff, true_iff] at h₁
      exfalso
      apply h₁
      clear h₁
      simp only [eq_iff_iff, true_iff] at h₂
      intro v hv
      simp only [mem_blockRelDistanceBall, SetLike.mem_coe] at hv
      simp only [IsMCA, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ge_iff_le,
        LinearCode.projectedWord, Fin.exists_fin_two,
        not_exists, not_and, not_or, not_not] at h₂
      let z := foldingBlockAgreement k ω α u0 u1 v
      have hz : 2 ^ (n - 1) * ((1 : ℝ) - ↑δ') ≤ ↑(#z) := by {
        simp only [z]
        exact le_trans' (card_foldingBlockAgreement_ge hk (by omega)) <| by
          norm_cast
          rw [NNReal.val_eq_coe, NNReal.coe_mul]
          conv_lhs =>
            lhs
            rw [show (Nat.cast (R := ℝ) _) = 2 ^ (n - 1) by simp]
          conv_rhs =>
            lhs
            rw [show (NNReal.toReal _) = 2 ^ (n - 1) by simp]
          field_simp
          have : u0 + α • u1 = foldWord ω f 1 α := by 
            aesop (add simp [foldWord_k_1'])
          rw [NNReal.coe_sub (by simp), show toReal 1 = 1 by simp,
              sub_le_sub_iff_left]
          aesop 
            (add simp [div_le_div_iff_left])
            (add unsafe (by rw [blockRelDistance_symm]))
      }
      specialize h₂ z hz (by {
        simpa using 
          LinearCode.restrict_mem_projectedCode_of_codeword_eq v hv.1 <| fun i hi ↦ by
            simp_all [z, Matrix.vecMul, UnivariatePowers, 
                      foldingBlockAgreement_is_agreement hk (by omega) hi]
      })
      simp only [LinearCode.mem_projectedCode_submod, LinearCode.mem_projectedCode, SetLike.mem_coe,
        Set.restrict_apply] at h₂
      obtain ⟨⟨u₀ᵣ, hu₀⟩, ⟨u₁ᵣ, hu₁⟩⟩ := h₂
      rw [mem_code_iff_exists_polynomial] at hu₀ hu₁
      obtain ⟨⟨u₀ₚ, hu₀ₚ⟩, hu₀⟩ := hu₀
      obtain ⟨⟨u₁ₚ, hu₁ₚ⟩, hu₁⟩ := hu₁
      have δ1 : δ < 1 := lt_of_lt_of_le δ_lt (by simp)
      have hball := mem_ball_of_u0_u1_polynomials
          (u₀ := u₀ₚ) (u₁ := u₁ₚ) (ω := ω) (f := f) (δ := δ)
          δ1 (d := d) (k := k) (z := foldingBlockAgreementᵣ k ω α u0 u1 v)
          (by grind) (by grind) hk hkd
          (card_foldingBlockAgreement_foldingBlockAgreementᵣ_le _ hk (n := n) (by omega) <| by
            simp only [z, δ'] at hz
            rw [←NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub (le_of_lt δ1)]
            norm_num
            exact hz )
      specialize hball (fun j hj ↦ by
        rw [agreement_on_z_of_u0_u1_polynomials (ω := ω) (f := f) (u₀ := u₀ₚ) (u₁ := u₁ₚ) (z := z)]
        · simp
        · aesop (add simp [foldWordEven, evalOnPoints])
        · aesop (add simp [foldWordOdd, evalOnPoints])
        · rw [mem_foldingBlockAgreementᵣ_of_mem_foldingBlockAgreement hk (by omega)]
          exact hj)
      simp only [_root_.map_add, evalOnPoints_mul, evalOnPoints_X, Embedding.coeFn_mk,
        mem_blockRelDistanceBall, SetLike.mem_coe, Set.mem_image] at hball ⊢
      exists (evalOnPoints (ω : Fin (2 ^ n) ↪ F) (u₀ₚ.comp (Y ^ 2) + Y * u₁ₚ.comp (Y ^ 2)))
      constructor
      · constructor
        · convert hball.1
          simp
        · convert hball.2
          simp
      · rw [foldWord_evalOnPoints (by omega) (by {
          exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) <| by
            simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos,
              degree_comp, degree_mul, sup_lt_iff]
            
})] 
        sorry -- no idea
    · simp



end ProximityGap

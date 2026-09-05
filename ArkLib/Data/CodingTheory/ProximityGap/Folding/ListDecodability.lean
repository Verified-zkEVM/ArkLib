/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Aristotle (Harmonic)
-/

import ArkLib.Data.CodingTheory.Basic.BlockRelDistance
import ArkLib.Data.CodingTheory.ProximityGap.Folding
import ArkLib.Data.CodingTheory.ProximityGap.Folding.FoldingContext
import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
import ArkLib.Data.Domain.CosetFftDomain.Pullback

/-!
# Folding preserves list decoding (WHIR Theorem 4.20)

Random folding of a smooth Reed-Solomon code preserves block list decoding: assuming the
generator `Gen(2; α) = (1, α)` has mutual correlated agreement for the folded codes
`C⁽¹⁾, …, C⁽ᵏ⁾`, the image of the block list of `f` under `k`-fold folding equals the list
of the folded word, except with probability at most the sum of the per-round MCA errors.

* `folding_preserves_block_balls` — Claim 4.22 of [ACFY24]: folding maps the block list of
  `f` into the block list of `Fold(f, α)`, for every `α`.
* `folding_reflects_balls` — Lemma 4.21: with probability `1 − ε_mca(δ)` over `α`, the two
  lists coincide after one folding round.
* `iterated_folding_reflects_balls` — Theorem 4.20: the `k`-round statement, by a union
  bound over the rounds.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
-/

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
  simp_all only [Word, blockRelDistanceBall, SetLike.mem_coe, Set.mem_ofPred_eq]
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
         k - 1, ω.subdomain 1, foldWord ω f 1 α, δ) := by
  rintro x ⟨u, hu, rfl⟩
  exact folding_block_rel_ball hu

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
      card_toFinset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
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

omit [DecidableEq F] in
/-- The rate of the Reed-Solomon code of degree `2 ^ d` on the halved domain, in closed form. -/
private lemma rate_folded_eq :
  (LinearCode.rate (code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ d)) : ℝ≥0)
    = ((min (2 ^ d) (2 ^ (n - 1)) : ℕ) : ℝ≥0) / ((2 : ℝ≥0) ^ (n - 1)) := by
  aesop (add simp ReedSolomon.rateOfLinearCode_eq_min_div)

omit [DecidableEq F] in
/-- A word whose projection to `T` lies in the projected Reed-Solomon code agrees on `T`
  with the evaluation of a polynomial of degree `< m`. -/
lemma exists_poly_of_projectedWord_mem {ι : Type}
    {dom : ι ↪ F} {m : ℕ} {w : ι → F} {T : Finset ι}
  (h : LinearCode.projectedWord w T ∈ LinearCode.projectedCodeSubmod (code dom m) T) :
  ∃ p : Polynomial F, p.degree < m ∧ ∀ t ∈ T, w t = p.eval (dom t) := by
  rw [LinearCode.mem_projectedCodeSubmod_iff] at h
  obtain ⟨c, hc, hcw⟩ := h
  replace hc : c ∈ code dom m := hc
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  refine ⟨p, hp, fun t ht => ?_⟩
  have := congrFun hcw ⟨t, ht⟩
  simpa [LinearCode.projectedWord, evalOnPoints] using this

omit [DecidableEq F] in
/-- The rate of the degree-`2 ^ d` code on the halved domain accounts for at least `2 ^ (d-1)`
  positions. -/
lemma two_pow_d_sub_one_le_rate_mul (hkd : 1 ≤ d) (hdn : d ≤ n) :
    ((2 : ℝ≥0) ^ (d - 1)) ≤
    2 ^ (n - 1) *
      (LinearCode.rate (code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1))) : ℝ≥0) := by
  rw [rate_folded_eq, mul_div_cancel₀ _ (by positivity)]
  have h1 : (2 : ℕ) ^ (d - 1) ≤ min (2 ^ (d - 1)) (2 ^ (n - 1)) :=
    le_min le_rfl (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact_mod_cast Nat.cast_le.2 h1

open CoreDefinitions unitInterval FoldingContext in
/-- Claim 4.23 from [ACFY24]. -/
private lemma folding_reflects_balls_aux [Fintype F] [FoldingContext k d n]
  {ε_mca : I → ℝ≥0}
  (hmca : IsMCAGenerator (univariatePowersGenerator F 1) ε_mca
    (ReedSolomon.code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1))))
  {δ : ℝ≥0}
  (_δ_gt_0 : 0 < δ)
  (δ_lt : δ <
    (1 - (LinearCode.rate
      (ReedSolomon.code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)))))) :
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
  intro δ'
  have hδ1 : δ < 1 := lt_of_lt_of_le δ_lt (by simp)
  have hrate := two_pow_d_sub_one_le_rate_mul (ω := ω) (d := d) (by grind)
    (by grind)
  have key : ∀ α : F,
      ¬ (blockRelDistanceBall (k - 1) (ω.subdomain 1) (foldWord ω f 1 α) δ
            (code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)))) ⊆
          Set.image (fun u ↦ foldWord ω u 1 α)
            (blockRelDistanceBall k ω f δ (code (ω : Fin (2 ^ n) ↪ F) (2 ^ d))) →
      IsMCA (univariatePowersGenerator F 1)
        (code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1))) α
        ![foldWordEven ω f, foldWordOdd ω f] (δ : ℝ) := by
    intro α hbad
    rw [Set.not_subset] at hbad
    obtain ⟨v, hv, hvimg⟩ := hbad
    simp only [blockRelDistanceBall, SetLike.mem_coe] at hv
    obtain ⟨hvC, hvdist⟩ := hv
    set u0 := foldWordEven ω f with hu0def
    set u1 := foldWordOdd ω f with hu1def
    have hsum : u0 + α • u1 = foldWord ω f 1 α :=
      foldWord_k_1_eq_foldWordEven_add_foldWordOdd.symm
    set T := foldingBlockAgreement k ω α u0 u1 v with hTdef
    have hTagree : ∀ i ∈ T, u0 i + α * u1 i = v i := fun i hi ↦
      foldingBlockAgreement_is_agreement hi
    have hvdist' : δ𞁒(k - 1, ω.subdomain 1, u0 + α • u1, v) ≤ δ := by aesop
    have hTcard : (2 : ℝ≥0) ^ (n - 1) * (1 - δ) ≤ (T.card : ℝ≥0) :=
      le_trans' card_foldingBlockAgreement_ge (by gcongr)
    have hcomb : ∀ i ∈ T,
        (∑ j, univariatePowersGenerator F 1 α j • ![u0, u1] j i) = v i := fun i hi ↦ by
      simpa [Fin.sum_univ_two, univariatePowersGenerator] using hTagree i hi
    refine ⟨T, ?_, ?_, ?_⟩
    · have h := NNReal.coe_le_coe.2 hTcard
      rw [NNReal.coe_mul, NNReal.coe_sub hδ1.le] at h
      simpa using h
    · rw [LinearCode.mem_projectedCodeSubmod_iff]
      refine ⟨v, hvC, ?_⟩
      funext t
      simp only [LinearCode.projectedWord, Set.domRestrict_apply]
      exact hcomb t.1 t.2
    · by_contra hcon
      push Not at hcon
      have h0 := hcon 0
      have h1 := hcon 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      obtain ⟨p₀, hp₀deg, hp₀⟩ := exists_poly_of_projectedWord_mem h0
      obtain ⟨p₁, hp₁deg, hp₁⟩ := exists_poly_of_projectedWord_mem h1
      have hzcard := card_foldingBlockAgreement_foldingBlockAgreementᵣ_le δ hTcard
      have hz : ∀ j : Fin (2 ^ n),
          ω j ^ 2 ^ k ∈ ω.subdomain k '' (foldingBlockAgreementᵣ k ω α u0 u1 v) →
          f j = p₀.eval (ω j ^ 2) + ω j * p₁.eval (ω j ^ 2) := by
        intro j hj
        rw [← mem_foldingBlockAgreementᵣ_of_mem_foldingBlockAgreement] at hj
        have hagr := agreement_on_z_of_u0_u1_polynomials (ω := ω) (f := f) (u₀ := p₀) (u₁ := p₁)
          T (fun i hi => by simpa [hu0def, foldWordEven, log_right_inverse'] using hp₀ i hi)
          (fun i hi => by simpa [hu1def, foldWordOdd, log_right_inverse'] using hp₁ i hi) hj
        simpa using hagr
      have huball := mem_ball_of_u0_u1_polynomials (ω := ω) (f := f) (k := k) (d := d)
        hδ1 hp₀deg hp₁deg (foldingBlockAgreementᵣ k ω α u0 u1 v) hzcard hz
      set w := evalOnPoints (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (p₀ + α • p₁) with hwdef
      have hwcode : w ∈ code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)) :=
        ReedSolomon.evalOnPoints_mem_code_of_degree_lt
          (lt_of_le_of_lt (Polynomial.degree_add_le _ _)
            (max_lt hp₀deg (lt_of_le_of_lt (Polynomial.degree_smul_le _ _) hp₁deg)))
      have hfoldw : foldWord ω (evalOnPoints (ω : Fin (2 ^ n) ↪ F)
          (p₀.comp (Polynomial.X ^ 2) + Polynomial.X * p₁.comp (Polynomial.X ^ 2))) 1 α = w := by
        funext i
        rw [foldWord_evalOnPoints_split]
        simp [hwdef, evalOnPoints]
      have hTdeg : 2 ^ (d - 1) ≤ T.card := by
        have hrate' :
          (LinearCode.rate (code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1))) : ℝ≥0)
            ≤ 1 - δ := le_of_lt (lt_tsub_comm.mp δ_lt)
        have h1 : ((2 : ℝ≥0) ^ (d - 1)) ≤ (T.card : ℝ≥0) := by
          refine le_trans hrate (le_trans ?_ hTcard)
          gcongr
        exact_mod_cast h1
      have hwv : w = v := by
        refine eq_of_agree_of_card_le hwcode hvC (T := T) hTdeg ?_
        intro t ht
        have hwt : w t = u0 t + α * u1 t := by
          rw [hp₀ t ht, hp₁ t ht, hwdef]
          simp [evalOnPoints]
        rw [hwt]
        exact hTagree t ht
      exact hvimg ⟨_, huball, hfoldw.trans hwv⟩
  exact le_trans (Probability.Pr_le_Pr_of_implies _ _ _ key)
    (by simpa using hmca.prob_le _ δ')

open CoreDefinitions unitInterval in
/-- **Lemma 4.21 of [ACFY24].** One folding round preserves block list decoding: if
  `Gen(2; α) = (1, α)` has mutual correlated agreement for `C' = RS[F, ω², 2^(d-1)]` with
  error `ε_mca`, then for `δ < 1 - rate(C')`, with probability at least `1 - ε_mca δ` over
  `α` the `(k-1)`-wise block list of `Fold(f, α)` is exactly the image under folding of the
  `k`-wise block list of `f`. One containment holds for every `α`
  (`folding_preserves_block_balls`, Claim 4.22); the other except with probability
  `ε_mca δ` (Claim 4.23). -/
theorem folding_reflects_balls [Fintype F] [FoldingContext k d n]
    {ε_mca : I → ℝ≥0}
  (hmca : IsMCAGenerator (univariatePowersGenerator F 1) ε_mca
    (ReedSolomon.code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1))))
  {δ : ℝ≥0}
  (_δ_gt_0 : 0 < δ)
  (δ_lt : δ <
    (1 - (LinearCode.rate
      (ReedSolomon.code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)))))) :
  let δ' : I := ⟨δ, by aesop, by {
              rw [show 1 = NNReal.toReal 1 by norm_cast, ←NNReal.toReal_le]
              exact le_trans (le_of_lt δ_lt) (by simp)}⟩
  Pr_{ let α ←$ᵖ F}[
    (Λ𞁒(code (ω.subdomain 1 : Fin (2 ^ (n - 1)) ↪ F) (2 ^ (d - 1)),
             k - 1, ω.subdomain 1, foldWord ω f 1 α, δ)) ≠
      Set.image
        (fun u ↦ foldWord ω u 1 α)
        (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), k, ω, f, δ))] ≤
          ENNReal.ofReal (ε_mca δ') := by
  extract_lets δ'
  refine le_trans'
    (folding_reflects_balls_aux (f := f) hmca _δ_gt_0 δ_lt)
    (Probability.Pr_le_Pr_of_implies _ _ _ ?_)
  intro α hne hsub
  exact hne (Set.Subset.antisymm hsub folding_preserves_block_balls)

open CoreDefinitions unitInterval in
/-- **Iterated folding reflects block relative distance lists.**
  Auxiliary form of the `k`-round theorem, with the block parameter `b` of the *target* list
  kept general so that the statement can be used inductively (the `k`-round process turns a
  `(b + k)`-wise block list into a `b`-wise block list).
  The `i`-th round is a single folding step on the `i`-th subdomain, and its failure
  probability is bounded by the mutual-correlated-agreement error `ε i` of the generator
  `Gen(2; α) = (1, α)` for the code `C^(i+1)`; the total failure probability is at most the sum
  of these errors. -/
private theorem iterated_folding_reflects_balls_aux [Fintype F] (k : ℕ) :
    ∀ (n d b : ℕ) (ω : SmoothCosetFftDomain n F) (f : Word F (Fin (2 ^ n)))
      (ε : ℕ → I → ℝ≥0) (δ : ℝ≥0) (hδ1 : δ ≤ 1),
      b + k ≤ d → d ≤ n → 0 < δ →
      (∀ i, i < k → IsMCAGenerator (univariatePowersGenerator F 1) (ε i)
        (code (ω.subdomain (i + 1) : Fin (2 ^ (n - (i + 1))) ↪ F) (2 ^ (d - i - 1)))) →
      (∀ i, i < k → δ < 1 - (LinearCode.rate
        (code (ω.subdomain (i + 1) : Fin (2 ^ (n - (i + 1))) ↪ F) (2 ^ (d - i - 1))) : ℝ≥0)) →
      Pr_{ let α ←$ᵖ (Fin k → F) }[
        Λ𞁒(code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k)), b, ω.subdomain k,
            iteratedFoldWord ω f k α, δ) ≠
          Set.image (fun u ↦ iteratedFoldWord ω u k α)
            (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), b + k, ω, f, δ))] ≤
        ∑ i ∈ Finset.range k, ENNReal.ofReal (ε i ⟨δ, δ.coe_nonneg, by exact_mod_cast hδ1⟩) := by
  induction k with
  | zero =>
      intro n d b ω f ε δ hδ1 hbd hdn hδ0 _ _
      refine le_of_eq (Probability.prob_eq_zero_of_forall_not _ _ fun α ↦ ?_)
      aesop
  | succ k ih =>
      intro n d b ω f ε δ hδ1 hbd hdn hδ0 hmca hrate
      classical
      set δ' : I := ⟨δ, δ.coe_nonneg, by exact_mod_cast hδ1⟩ with hδ'
      have hk1n : k + 1 ≤ n := by omega
      have hsub : (ω.subdomain k).subdomain 1 = ω.subdomain (k + 1) :=
        subdomain_subdomain_one (by omega)
      -- the per-round bound for the last round, on the `k`-th subdomain
      have hlast : ∀ w : Word F (Fin (2 ^ (n - k))),
          Pr_{ let x ←$ᵖ F }[
            Λ𞁒(code ((ω.subdomain k).subdomain 1 : Fin (2 ^ (n - k - 1)) ↪ F) (2 ^ (d - k - 1)),
                b + 1 - 1, (ω.subdomain k).subdomain 1,
                foldWord (ω.subdomain k) w 1 x, δ) ≠
              Set.image (fun u ↦ foldWord (ω.subdomain k) u 1 x)
                (Λ𞁒(code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k)), b + 1,
                    ω.subdomain k, w, δ))] ≤ ENNReal.ofReal (ε k δ') := by
        intro w
        have hm := hmca k (by omega)
        have hr := hrate k (by omega)
        rw [← hsub] at hm hr
        have : FoldingContext (b + 1) (d - k) (n - k) := FoldingContext.mk'
          (by omega) (by omega) (by omega)
        exact folding_reflects_balls (ω := ω.subdomain k) (f := w) (k := b + 1)
          (d := d - k) (n := n - k) hm hδ0 hr
      rw [Probability.prob_fin_succ_split]
      refine le_trans (Probability.tsum_prob_le_add _ _
        (fun y => Λ𞁒(code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k)), b + 1,
            ω.subdomain k, iteratedFoldWord ω f k y, δ) ≠
          Set.image (fun u ↦ iteratedFoldWord ω u k y)
            (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), b + 1 + k, ω, f, δ)))
        (ENNReal.ofReal (ε k δ')) ?_) ?_
      · -- the conditional bound, for each value `y` of the first `k` rounds' randomness
        intro y
        by_cases hy : Λ𞁒(code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k)), b + 1,
            ω.subdomain k, iteratedFoldWord ω f k y, δ) ≠
          Set.image (fun u ↦ iteratedFoldWord ω u k y)
            (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), b + 1 + k, ω, f, δ))
        · rw [if_pos hy]
          exact le_trans (Probability.prob_le_one _ _) le_self_add
        · rw [if_neg hy, zero_add]
          rw [not_not] at hy
          refine le_trans (Probability.Pr_le_Pr_of_implies _ _ _ ?_)
            (hlast (iteratedFoldWord ω f k y))
          intro x hx
          have hfold : ∀ u : Word F (Fin (2 ^ n)),
              iteratedFoldWord ω u (k + 1) (Fin.snoc y x) =
                foldWord (ω.subdomain k) (iteratedFoldWord ω u k y) 1 x := by
            intro u
            rw [iteratedFoldWord_succ']
            simp only [Fin.snoc_castSucc, Fin.snoc_last]
          have himg : Set.image (fun u ↦ iteratedFoldWord ω u (k + 1) (Fin.snoc y x))
              (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), b + (k + 1), ω, f, δ)) =
              Set.image (fun u ↦ foldWord (ω.subdomain k) u 1 x)
                (Set.image (fun u ↦ iteratedFoldWord ω u k y)
                  (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), b + 1 + k, ω, f, δ))) := by
            rw [← Set.image_comp, show b + (k + 1) = b + 1 + k by omega]
            exact Set.image_congr' (fun u => hfold u)
          intro hcon
          apply hx
          rw [himg, ← hy, ← hcon, hfold f, hsub]
          rfl
      · -- the union bound over the rounds
        have hih := ih n d (b + 1) ω f ε δ hδ1 (by omega) hdn hδ0
          (fun i hi => hmca i (by omega)) (fun i hi => hrate i (by omega))
        rw [Finset.sum_range_succ]
        gcongr

open CoreDefinitions unitInterval in
/-- **Theorem 4.20 of [ACFY24].** Let `C = RS[F, ω, 2 ^ d]` be a smooth Reed-Solomon code and
  `k ≤ d`, and let `C⁽ⁱ⁾ = RS[F, ω^(2 ^ i), 2 ^ (d - i)]`. If `Gen(2; α) = (1, α)` is a proximity
  generator with mutual correlated agreement for `C⁽¹⁾, …, C⁽ᵏ⁾` with errors `ε 0, …, ε (k-1)`,
  then for every `f` and every `δ < 1 - rate(C⁽ⁱ⁾)` for each `i`,
  `Pr_α [ Fold(Λ_b(C, k, f, δ), α) ≠ Λ(C⁽ᵏ⁾, Fold(f, α), δ) ] ≤ ∑ i < k, ε i δ`.
  The `k` rounds of randomness are sampled independently and uniformly, and the bound is the
  union bound over the per-round failure probabilities of `folding_reflects_balls`.

  The paper states the range as `δ < 1 - B⋆(C⁽ⁱ⁾, 2)`; here the mutual-correlated-agreement
  error is total in `δ`, so only the rate bound `1 - rate(C⁽ⁱ⁾)` is needed to make the codewords
  explaining the folded agreement unique. Every regime proposed in the paper has
  `B⋆ ≥ rate` (with equality in the capacity regime), so the paper's range implies this one. -/
theorem iterated_folding_reflects_balls [Fintype F]
    [FoldingContext k d n]
    {ω : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))}
    (ε : ℕ → I → ℝ≥0) {δ : ℝ≥0} (hδ1 : δ ≤ 1) (hδ0 : 0 < δ)
    (hmca : ∀ i, i < k → IsMCAGenerator (univariatePowersGenerator F 1) (ε i)
      (code (ω.subdomain (i + 1) : Fin (2 ^ (n - (i + 1))) ↪ F) (2 ^ (d - i - 1))))
    (hrate : ∀ i, i < k → δ < 1 - (LinearCode.rate
      (code (ω.subdomain (i + 1) : Fin (2 ^ (n - (i + 1))) ↪ F) (2 ^ (d - i - 1))) : ℝ≥0)) :
    Pr_{ let α ←$ᵖ (Fin k → F) }[
      Set.image (fun u ↦ iteratedFoldWord ω u k α)
          (Λ𞁒(code (ω : Fin (2 ^ n) ↪ F) (2 ^ d), k, ω, f, δ)) ≠
        {v | v ∈ (code (ω.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k)) :
              Set (Fin (2 ^ (n - k)) → F)) ∧
            ((δᵣ(iteratedFoldWord ω f k α, v) : ℚ≥0) : ℝ≥0) ≤ δ}] ≤
      ∑ i ∈ Finset.range k, ENNReal.ofReal (ε i ⟨δ, δ.coe_nonneg, by exact_mod_cast hδ1⟩) := by
  have h := iterated_folding_reflects_balls_aux (F := F) k n d 0 ω f ε δ hδ1
    (by grind) (by grind) hδ0 hmca hrate
  refine le_trans (Probability.Pr_le_Pr_of_implies _ _ _ ?_) h
  aesop (add simp blockRelDistanceBall_zero)

end ProximityGap

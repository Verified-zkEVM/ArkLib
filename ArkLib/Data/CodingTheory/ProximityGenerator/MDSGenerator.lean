/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
public import ArkLib.Data.CodingTheory.ProximityGenerator.ExceptionalSet
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import ArkLib.Data.Finset.PairwiseIntersection
public import ArkLib.Data.Finset.TupleIntersection

/-!
# Mutual correlated agreement for MDS generators

Every MDS generator whose code has full dimension `ℓ ≥ 2` has mutual correlated agreement for
every module code, with error `mdsMCAError` (Theorem 6.1 [BCGM25]). Both regimes are proved:
the unique-decoding regime by `mcaError_le_mdsMCAError_of_lt`, the list-decoding regime by the
seed count `card_filter_isMCA_le_of_isMDSGenerator_of_le_one_sub`, which partitions the bad seeds
and bounds the parts by Claims 6.7–6.9 [BCGM25].

## Main statements

* `mdsMCAError` — the MCA error function of an MDS generator, with `mdsMCAError_congr` showing it
  depends on the code only through its block length and relative distance.
* `exists_codewordSpan_of_isMDSGenerator` — codewords agreeing with `ℓ` generated words on a
  common set are recovered as a codeword span, which captures every other codeword that agrees
  with a generated word on a large enough set (Lemma 5.2 [BCGM25]).
* `hammingDist_lt_of_isMDSGenerator` — if many seeds bring the generated words of two families
  close, the families themselves are close (Lemma 5.3 [BCGM25]).
* `card_filter_isMCA_le_of_isMDSGenerator` — the seed count behind the unique-decoding regime: at
  most `(⌊n·γ⌋ + 1)·(ℓ - 1)` seeds witness the MCA event for a fixed word family.
* `mcaError_le_mdsMCAError_of_lt` — MCA for MDS generators in the unique-decoding regime
  (Lemma 6.2 [BCGM25], with the corrected bound below): the `mdsMCAError` bound at every radius
  below `δ_C / (ℓ + 1)`.
* `subset_isMaxAgreementDomain_of_isMDSGenerator` — at any seed, a set on which the generated
  word lies in the projected code and which overlaps the intersection of `ℓ` maximal agreement
  domains in all but fewer than `d_C` positions lies in every such-overlapping maximal agreement
  domain of that word (the step of [BCGM25] cited as "from the proof of Lemma 6.4").
* `isMaxCADomain_inf_of_isMDSGenerator` — `ℓ` maximal agreement domains
  (`LinearCode.IsMaxAgreementDomain`, Definition 6.3 [BCGM25]) at distinct seeds, intersecting
  in all but fewer than `d_C` positions, intersect in a maximal CA domain (Lemma 6.4 [BCGM25]).
* `inf_isMaxAgreementDomain_eq_of_isMDSGenerator` — any `ℓ` maximal agreement domains containing
  a large maximal CA domain intersect exactly in it (Lemma 6.5 [BCGM25]).
* `sum_card_sdiff_le_pred_mul_card_compl_of_isMDSGenerator` — maximal agreement domains at
  distinct seeds containing a large maximal CA domain `A₀` have total size at most
  `(ℓ - 1)·|A₀ᶜ|` outside `A₀`; this is the form Claim 6.9 consumes.
* `card_le_pred_mul_card_compl_of_isMDSGenerator` — at most `(ℓ - 1)·|A₀ᶜ|` seeds have a maximal
  agreement domain strictly containing the maximal CA domain `A₀` (Lemma 6.6 [BCGM25]).
* `card_filter_isMaxCADomain_mul_le_one` — at most `1 / η` maximal CA domains are large
  (Claim 6.7 [BCGM25]), by the Corrádi bound.
* `card_le_of_ssubset_isMaxAgreementDomain_of_isMDSGenerator` — few seeds strictly extend a large
  maximal CA domain (Claim 6.8 [BCGM25]).
* `card_mul_le_of_forall_not_subset_of_isMDSGenerator` — few seeds avoid every large maximal CA
  domain (Claim 6.9 [BCGM25]), via the dense-intersection lemma
  `Finset.exists_injective_two_mul_card_filter_lt_card_inf_inter`.
* `card_filter_isMCA_le_of_isMDSGenerator_of_le_one_sub` — the seed count behind the
  list-decoding regime.
* `isMCAGenerator_of_isMDSGenerator` — MCA for MDS generators at every radius (Theorem 6.1
  [BCGM25]).

The correspondence to [BCGM25]'s numbered statements is in
`docs/kb/audits/bcgm25-mca-generators.md`.

## Departure from [BCGM25]: Fable Audit

Lemma 6.2 of [BCGM25] prints the unique-decoding error as `max{n·γ, 1}·(ℓ - 1) / |S|`. That
bound is false whenever `1 ≤ ⌊n·γ⌋`: for the affine line generator `x ↦ (1, x)` and words
`u₁ = η₁`, `u₂ = η₂` supported on a common set of `⌊n·γ⌋ + 1` positions with pairwise distinct
ratios `η₁[i] / η₂[i]`, each of the `⌊n·γ⌋ + 1` seeds `x = -η₁[i] / η₂[i]` cancels position
`i` and witnesses the MCA event at radius `γ`, exceeding the printed `n·γ·(ℓ - 1) = ⌊n·γ⌋` when
`n·γ` is an integer. The error is therefore stated with `⌊n·γ⌋ + 1` in place of `max{n·γ, 1}`;
the two agree below `1/n`, and the corrected bound is attained by the example above. The paper's
argument, which the proof here follows, yields exactly this count: its step "`|T̃| > n·(1 - γ)`"
only follows in the weak form `n - |T̃| ≤ ⌊n·γ⌋`.

## References

* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
    with Mutual Correlated Agreement*][BCGM25]
-/

@[expose] public section

open NNReal unitInterval LinearCode CoreDefinitions

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {A : Type} [AddCommMonoid A] [Module F A]
         {ℓ : Type} [Fintype ℓ]

/-- The MCA error function of an MDS generator with output size `ℓ` and `s` seeds, for a module
code `MC`, at slack parameter `η`. As a function of the proximity parameter `γ` it is a step
function with three regimes: a unique-decoding bound `(⌊n·γ⌋ + 1)·(ℓ - 1) / s` below
`δ_C / (ℓ + 1)`, a list-decoding bound up to `1 - (ρ_C + η) ^ (1 / (ℓ + 1))`, and the trivial
bound `1` beyond. The unique-decoding regime replaces the paper's `max{n·γ, 1}` by `⌊n·γ⌋ + 1`. -/
noncomputable def mdsMCAError [DecidableEq F] [DecidableEq A] [Nonempty ι] (MC : ModuleCode ι F A)
  (ℓ s : ℕ) (η : ℝ) : I → ℝ≥0 :=
  letI n : ℝ := Fintype.card ι
  letI δ_C : ℝ := (Code.minRelHammingDistCode (MC.carrier) : ℝ)
  letI ρ_C : ℝ := 1 - δ_C
  letI γ_ℓ : ℝ := 1 - (ρ_C + η) ^ (1 / ℓ : ℝ)
  fun γ =>
    Real.toNNReal <|
      if γ < (δ_C / (ℓ + 1) : ℝ) then
        letI m' : ℝ := ⌊n * γ⌋₊ + 1
        m' * ((ℓ - 1) / s : ℝ)
      else
        if γ ≤ 1 - (ρ_C + η) ^ (1 / (ℓ + 1) : ℝ) then
            (n * γ_ℓ / η) * ((ℓ - 1) / s) +
            max (2 * (ℓ - 1) /
                  (η * ((ρ_C + η) ^ (1 / ((ℓ + 1) : ℝ)) - (ρ_C + η) ^ (1 / ℓ : ℝ)) * s))
                (ℓ * (ℓ + 1) / (η * s) : ℝ)
        else
        1

/-- `mdsMCAError` reads the code only through the block length `ι` and the relative distance
`δᵣ`. -/
lemma mdsMCAError_congr [DecidableEq F] [Nonempty ι] {A' : Type} [DecidableEq A]
    [AddCommMonoid A'] [Module F A'] [DecidableEq A']
    (MC : ModuleCode ι F A) (MC' : ModuleCode ι F A') (ℓ s : ℕ) (η : ℝ)
    (hδ : Code.minRelHammingDistCode MC'.carrier = Code.minRelHammingDistCode MC.carrier) :
    mdsMCAError MC' ℓ s η = mdsMCAError MC ℓ s η := by
  unfold mdsMCAError
  rw [hδ]

section ListDecodingRadii

/-! ### Arithmetic of the list-decoding radii

The list-decoding regime of `mdsMCAError` is phrased through the radii
`γ_ℓ = 1 - (ρ_C + η) ^ (1 / ℓ)` and `γ = 1 - (ρ_C + η) ^ (1 / (ℓ + 1))`. The three facts below are
every `Real.rpow` property the regime needs; collecting them here keeps `rpow` out of the
combinatorial lemmas, which are stated at abstract thresholds instead.

Throughout, `ρ` stands for `ρ_C = 1 - δ_C`, which is the pairwise-intersection density the
Corrádi step reads, and `η` for the slack. -/

/-- `ρ < (ρ + η) ^ (1 / L)` for `L ≥ 1`: the radius `γ_L = 1 - (ρ + η) ^ (1 / L)` stays below the
relative distance `δ_C = 1 - ρ`. Consumed wherever a maximal CA domain of size at least
`n · (1 - γ_L)` must miss fewer than `d_C` positions. -/
lemma lt_rpow_one_div (ρ η : ℝ) (L : ℕ) (hρ : 0 ≤ ρ) (hη : 0 < η) (h1 : ρ + η ≤ 1)
    (hL : 1 ≤ L) :
    ρ < (ρ + η) ^ (1 / L : ℝ) := by
  have hb : 0 < ρ + η := by linarith
  calc ρ < ρ + η := by linarith
    _ = (ρ + η) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (ρ + η) ^ (1 / L : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hb h1
          (by rw [div_le_one (by positivity)]; exact_mod_cast hL)

/-- `ρ + η ≤ (ρ + η) ^ (2 / L)` for `L ≥ 2`: the Corrádi gap `α² - ρ` at `α = (ρ + η) ^ (1 / L)`
is at least `η`, which is what turns the incidence bound into the paper's `m · η ≤ 1`. -/
lemma le_rpow_two_div (ρ η : ℝ) (L : ℕ) (hρ : 0 ≤ ρ) (hη : 0 < η) (h1 : ρ + η ≤ 1)
    (hL : 2 ≤ L) :
    ρ + η ≤ (ρ + η) ^ (2 / L : ℝ) := by
  have hb : 0 < ρ + η := by linarith
  calc ρ + η = (ρ + η) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (ρ + η) ^ (2 / L : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hb h1
          (by rw [div_le_one (by positivity)]; exact_mod_cast hL)

/-- `(ρ + η) ^ (1 / L) < (ρ + η) ^ (1 / (L + 1))` when `ρ + η < 1`: the two list-decoding radii are
distinct, so the margin `(ρ + η) ^ (1 / (L + 1)) - (ρ + η) ^ (1 / L)` appearing in `mdsMCAError`
is positive. Strictness fails at `ρ + η = 1`, where both radii are `0`. -/
lemma rpow_one_div_lt_rpow_one_div_succ (ρ η : ℝ) (L : ℕ) (hρ : 0 ≤ ρ) (hη : 0 < η)
    (h1 : ρ + η < 1) (hL : 1 ≤ L) :
    (ρ + η) ^ (1 / L : ℝ) < (ρ + η) ^ (1 / (L + 1) : ℝ) := by
  have hb : 0 < ρ + η := by linarith
  refine Real.rpow_lt_rpow_of_exponent_gt hb h1 ?_
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rw [div_lt_div_iff₀ (by positivity) hLR]
  linarith

/-- `((x) ^ (1 / (L + 1))) ^ (L + 1) = x`: the radius `γ = 1 - (ρ + η) ^ (1 / (L + 1))` satisfies
`(1 - γ) ^ (L + 1) = ρ + η`. This is the identity behind the expected `(L + 1)`-wise intersection
`n · (1 - γ) ^ (L + 1) = n · (ρ + η)` in Claim 6.9. -/
lemma rpow_one_div_succ_pow (x : ℝ) (L : ℕ) (hx : 0 ≤ x) :
    (x ^ (1 / (L + 1) : ℝ)) ^ (L + 1) = x := by
  have h := Real.rpow_inv_natCast_pow hx (Nat.succ_ne_zero L)
  push_cast at h
  rwa [one_div]

/-- **The list-decoding branch has no degenerate cases.** If a radius `γ ≥ 0` lies in the
list-decoding branch of `mdsMCAError`, that is `δ / (L + 1) ≤ γ ≤ 1 - (1 - δ + η) ^ (1 / (L + 1))`,
then `ρ + η < 1` strictly, where `ρ = 1 - δ`.

So the branch never meets `ρ + η = 1`, where the two radii coincide and the margin
`(ρ + η) ^ (1 / (L + 1)) - (ρ + η) ^ (1 / L)` in `mdsMCAError` vanishes; nor `δ = 0`. If
`ρ + η ≥ 1`, the upper limit is at most `0`, so `γ = 0`, so `δ ≤ 0`; then `ρ + η ≥ 1 + η > 1`
puts the upper limit strictly below `0`, contradicting `γ ≥ 0`. -/
lemma one_sub_add_lt_one_of_le_one_sub_rpow (δ η γ : ℝ) (L : ℕ) (hη : 0 < η) (hγ0 : 0 ≤ γ)
    (hlow : δ / (L + 1) ≤ γ) (hup : γ ≤ 1 - (1 - δ + η) ^ (1 / (L + 1) : ℝ)) :
    1 - δ + η < 1 := by
  by_contra! h
  have hexp : (0 : ℝ) < 1 / (L + 1) := by positivity
  have hγ : γ = 0 := le_antisymm (by linarith [Real.one_le_rpow h hexp.le]) hγ0
  have hδ : δ ≤ 0 := by
    have hL : (0 : ℝ) < L + 1 := by positivity
    have := hγ ▸ hlow
    rwa [div_le_iff₀ hL, zero_mul] at this
  linarith [Real.one_lt_rpow (show (1 : ℝ) < 1 - δ + η by linarith) hexp]

end ListDecodingRadii

/-- A nonzero `v : ℓ → F` is orthogonal to `G x` for at most `|ℓ| - 1` seeds `x`: the codeword
`x ↦ G x ⬝ᵥ v` of `C_G` is nonzero, since `C_G` has dimension `|ℓ|`, so its weight is at least the
MDS distance `|S| - |ℓ| + 1`.

Lemma 3.13 [BCGM25], field form. The paper's single statement is split across two lemmas, because
it has to hold at two different alphabets; the module form is
`card_filter_sum_smul_eq_le_of_isMDSGenerator`. Both are stated as seed counts rather than as an
`IsZeroEvadingGenerator` error, which is the form the proofs below consume. -/
lemma card_filter_dotProduct_eq_zero_le_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    {v : ℓ → F} (hv : v ≠ 0) :
    (Finset.univ.filter fun x => G x ⬝ᵥ v = 0).card ≤ Fintype.card ℓ - 1 := by
  have hinj : Function.Injective (M_G G).mulVec :=
    Matrix.mulVec_injective_iff.mpr <| linearIndependent_iff_card_eq_finrank_span.mpr <| by
      rw [Set.finrank, ← Matrix.rank_eq_finrank_span_cols]; exact hdim.symm
  have hne : (M_G G).mulVec v ≠ 0 := fun h => hv (hinj (h.trans (Matrix.mulVec_zero _).symm))
  have hdist : Code.dist (LinearCode.fromColGenMat (M_G G)).carrier
      = Fintype.card S - Fintype.card ℓ + 1 := by rw [← hdim]; exact hG
  have hmem : (M_G G).mulVec v ∈ (LinearCode.fromColGenMat (M_G G)).carrier := ⟨v, rfl⟩
  have hwt : Code.dist (LinearCode.fromColGenMat (M_G G)).carrier
      ≤ hammingNorm ((M_G G).mulVec v) :=
    not_lt.mp fun h => hne <| Code.eq_of_lt_dist hmem (Submodule.zero_mem _) <|
      (hammingDist_zero_right _).trans_lt h
  have hsupp : hammingNorm ((M_G G).mulVec v)
      = (Finset.univ.filter fun x => ¬ G x ⬝ᵥ v = 0).card := rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
    fun x => G x ⬝ᵥ v = 0
  rw [Finset.card_univ] at hsplit
  omega

/-- The invertibility of any `|ℓ|` distinct rows of the generator matrix
of an MDS generator with `C_G` of dimension `|ℓ|`: a vector in the kernel would give a codeword
of `C_G` vanishing at `|ℓ|` seeds.

This is a version of Lemma 3.6 [BCGM25]: the direction from MDS to independence, specialised at
`k = |ℓ|`. -/
lemma isUnit_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq ℓ] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    {xs : ℓ → S} (hxs : Function.Injective xs) :
    IsUnit (Matrix.of fun k j => G (xs k) j) := by
  refine Matrix.mulVec_injective_iff_isUnit.mp
    ((injective_iff_map_eq_zero (Matrix.mulVecLin _)).mpr fun v hv => by_contra fun hne => ?_)
  have hle := card_filter_dotProduct_eq_zero_le_of_isMDSGenerator G hG hdim hne
  have hge : Fintype.card ℓ ≤ (Finset.univ.filter fun x => G x ⬝ᵥ v = 0).card :=
    Finset.card_univ (α := ℓ) ▸ Finset.card_le_card_of_injOn xs
      (fun k _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun hv k⟩) hxs.injOn
  have hpos : 0 < Fintype.card ℓ := Fintype.card_pos_iff.mpr ⟨(Function.ne_iff.mp hne).choose⟩
  omega

/-- Combining a module-valued family `v` against the rows of `M` and then against the rows of a
left inverse `N` of `M` recovers `v`: this is `N * M = 1` acting on `ℓ → A`. -/
lemma sum_smul_sum_smul_eq_of_mul_eq_one [DecidableEq ℓ] {N M : Matrix ℓ ℓ F} (h : N * M = 1)
    (v : ℓ → A) (j : ℓ) : ∑ k, N j k • ∑ j', M k j' • v j' = v j := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply]

/-- Two distinct families `v w : ℓ → A` have equal combinations
`∑ j, G x j • v j = ∑ j, G x j • w j` for at most `|ℓ| - 1` seeds `x`, since any `|ℓ|` seeds give an
invertible matrix through which `v` and `w` are recovered from the combinations.

This is the module form of Lemma 3.13 [BCGM25]. -/
lemma card_filter_sum_smul_eq_le_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] [DecidableEq A] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    {v w : ℓ → A} (hvw : v ≠ w) :
    (Finset.univ.filter fun x => ∑ j, G x j • v j = ∑ j, G x j • w j).card
      ≤ Fintype.card ℓ - 1 := by
  classical
  by_contra! hlt
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := ℓ)
    (β := (Finset.univ.filter fun x => ∑ j, G x j • v j = ∑ j, G x j • w j))
    (by rw [Fintype.card_coe]; omega)
  have hf : Function.Injective fun k => (f k).1 := Subtype.val_injective.comp f.injective
  set M : Matrix ℓ ℓ F := Matrix.of fun k j => G (f k).1 j with hM
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M
    ((Matrix.isUnit_iff_isUnit_det M).mp (isUnit_of_isMDSGenerator G hG hdim hf))
  refine hvw (funext fun j => ?_)
  rw [← sum_smul_sum_smul_eq_of_mul_eq_one hNM v j, ← sum_smul_sum_smul_eq_of_mul_eq_one hNM w j]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := (Finset.mem_filter.mp (f k).2).2
  simp only [hM, Matrix.of_apply]
  rw [hk]

/-- **Lemma 5.2 [BCGM25]** (codeword span). Let `G` be an MDS generator whose code has full
dimension `|ℓ|`, let `xs` be `|ℓ|` distinct seeds, and let each codeword `c k` agree with the
generated word `∑ j, G (xs k) j • U j` on a common set `A₀`. Inverting the seed matrix gives
codewords `cs` such that:
* each `U j` agrees with `cs j` on `A₀`;
* any codeword `c'` agreeing with a generated word `∑ j, G x j • U j` on a set `T'`, where
  `A₀ ∩ T'` misses fewer than `d_C` positions, is the span codeword `∑ j, G x j • cs j`.

The paper's hypothesis `|A₁ ∩ ⋯ ∩ A_{ℓ+1}| > n - Δ_C` is stated as
`|(A₀ ∩ T')ᶜ| < d_C`, with `A₀` any set inside the first `ℓ` agreement sets. -/
lemma exists_codewordSpan_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq ι] [DecidableEq A] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {xs : ℓ → S} (hxs : Function.Injective xs)
    {c : ℓ → ι → A} (hc : ∀ k, c k ∈ MC) {A₀ : Finset ι}
    (hA₀ : ∀ k, ∀ i ∈ A₀, ∑ j, G (xs k) j • U j i = c k i) :
    ∃ cs : ℓ → ι → A, (∀ j, cs j ∈ MC) ∧ (∀ j, ∀ i ∈ A₀, U j i = cs j i) ∧
      ∀ x, ∀ c' ∈ MC, ∀ T' : Finset ι, (∀ i ∈ T', ∑ j, G x j • U j i = c' i) →
        ((A₀ ∩ T')ᶜ).card < Code.minDist MC.carrier → c' = ∑ j, G x j • cs j := by
  classical
  set M : Matrix ℓ ℓ F := Matrix.of fun k j => G (xs k) j with hM
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M
    ((Matrix.isUnit_iff_isUnit_det M).mp (isUnit_of_isMDSGenerator G hG hdim hxs))
  set cs : ℓ → ι → A := fun j => ∑ k, M⁻¹ j k • c k with hcs
  have hcs_mem : ∀ j, cs j ∈ MC := fun j =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hc k)
  have hU_cs : ∀ j, ∀ i ∈ A₀, U j i = cs j i := fun j i hi => by
    rw [← sum_smul_sum_smul_eq_of_mul_eq_one hNM (fun j' => U j' i) j]
    simp only [hcs, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hM, Matrix.of_apply]
    rw [hA₀ k i hi]
  refine ⟨cs, hcs_mem, hU_cs, fun x c' hc' T' hT' hcard => ?_⟩
  refine Code.eq_of_disagreementCols_subset_of_card_lt_minDist hc'
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs_mem j)) _
    (fun i hi => Finset.mem_compl.mpr fun hiA => Code.mem_disagreementCols.mp hi ?_) hcard
  rw [← hT' i (Finset.mem_inter.mp hiA).2, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, hU_cs j i (Finset.mem_inter.mp hiA).1]

/-- **Lemma 5.3 [BCGM25]**, for MDS generators. Let `1 ≤ t ≤ e`. If, at more than
`(e / t)·(|ℓ| - 1)` seeds `x`, the generated words `∑ j, G x j • U j` and `∑ j, G x j • c j`
are within distance `e - t`, then the families `U` and `c` disagree in fewer than `e` coordinates.

The paper states this for a zero-evading generator with error `ε`; for an MDS generator the
seed count `ε·|S| = |ℓ| - 1` of Lemma 3.13 (`card_filter_sum_smul_eq_le_of_isMDSGenerator`) is used
directly. The interleaved distance `Δ_{Σ^ℓ}(U, c)` is the Hamming distance of the transposed
families. The words `c` need not be codewords.

Double counting: every disagreement coordinate is cancelled by at most `|ℓ| - 1` seeds, and every
seed in `X` leaves at most `e - t` coordinates uncancelled. -/
lemma hammingDist_lt_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq A] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (U c : ℓ → (ι → A)) (X : Finset S) {e t : ℕ} (ht : t ≤ e)
    (hX : ∀ x ∈ X,
      hammingDist (fun i => ∑ j, G x j • U j i) (fun i => ∑ j, G x j • c j i) ≤ e - t)
    (hcard : e * (Fintype.card ℓ - 1) < t * X.card) :
    hammingDist (fun i j => U j i) (fun i j => c j i) < e := by
  classical
  set r := Fintype.card ℓ - 1
  set E := Code.disagreementCols (fun i j => U j i) (fun i j => c j i)
  set Y : ι → Finset S :=
    fun i => Finset.univ.filter fun x => ∑ j, G x j • U j i = ∑ j, G x j • c j i
  have hY_card : ∀ i ∈ E, (Y i).card ≤ r := fun i hi =>
    card_filter_sum_smul_eq_le_of_isMDSGenerator G hG hdim (Code.mem_disagreementCols.mp hi)
  have hm : ∀ i ∈ E, X.card - r ≤ (X.bipartiteAbove (fun i x => x ∉ Y i) i).card := fun i hi =>
    (Nat.sub_le_sub_left (hY_card i hi) _).trans ((Finset.le_card_sdiff _ _).trans_eq
      (congrArg Finset.card Finset.filter_notMem_eq_sdiff.symm))
  have hn : ∀ x ∈ X, (E.bipartiteBelow (fun i x => x ∉ Y i) x).card ≤ e - t := fun x hx =>
    (Finset.card_le_card fun i hi => Code.mem_disagreementCols.mpr fun h =>
      ((Finset.mem_bipartiteBelow fun i x => x ∉ Y i).mp hi).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)).trans
      ((Code.hammingDist_eq_disagreementCols_card _ _).symm.trans_le (hX x hx))
  have hβ := Finset.card_mul_le_card_mul _ hm hn
  rw [Code.hammingDist_eq_disagreementCols_card]
  by_contra! hE
  rcases le_total X.card r with hXr | hrX
  · nlinarith [Nat.mul_le_mul_left t hXr, Nat.mul_le_mul_right r ht]
  · zify [hrX, ht] at hβ hcard hE
    nlinarith [mul_le_mul_of_nonneg_right hE (sub_nonneg.mpr (by exact_mod_cast hrX) :
      (0 : ℤ) ≤ X.card - r)]

open Classical in
/-- For `γ < δ_C / (|ℓ| + 1)` and any family `U`, at most `(⌊n·γ⌋ + 1)·(|ℓ| - 1)` seeds `x` satisfy
the MCA event `IsMCA G MC x U γ`.
Lemma 6.2 [BCGM25], with the corrected bound. -/
lemma card_filter_isMCA_le_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq A] [Nonempty ι] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (hℓ : 2 ≤ Fintype.card ℓ) (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < (Code.minRelHammingDistCode MC.carrier : ℝ) / (Fintype.card ℓ + 1)) :
    (Finset.univ.filter fun x => IsMCA G MC x U γ).card
      ≤ (⌊γ * Fintype.card ι⌋₊ + 1) * (Fintype.card ℓ - 1) := by
  have hδ := congrArg (Rat.cast (K := ℝ))
    (Code.minDist_div_card_eq_minRelHammingDistCode MC.carrier)
  push_cast at hδ
  set n := Fintype.card ι
  set L := Fintype.card ℓ
  set r := L - 1
  set e := ⌊γ * n⌋₊
  set B := Finset.univ.filter fun x => IsMCA G MC x U γ
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have he_le : (e : ℝ) ≤ γ * n := Nat.floor_le (by positivity)
  rw [← hδ, div_div, lt_div_iff₀ (by positivity)] at hγ
  have hd : e + L * e < Code.minDist MC.carrier := by
    exact_mod_cast (by nlinarith : (e : ℝ) + L * e < Code.minDist MC.carrier)
  by_contra! hlt
  have hrB : r < B.card := lt_of_le_of_lt (Nat.le_mul_of_pos_left r (Nat.succ_pos e)) hlt
  have hbad : ∀ x ∈ B, ∃ T : Finset ι, ∃ c ∈ MC, Tᶜ.card ≤ e ∧
      (∀ i ∈ T, ∑ j, G x j • U j i = c i) ∧
      ∃ j, projectedWord (U j) T ∉ projectedCodeSubmod MC T := fun x hx => by
    obtain ⟨T, hT, hmem, hj⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨c, hc, hcT⟩ := (mem_projectedCodeSubmod_iff MC T _).mp hmem
    exact ⟨T, c, hc,
      (Finset.card_compl T).trans_le ((mul_one_sub_le_card_iff_sub_card_le_floor T hγ0).mp hT),
      fun i hi => congrFun hcT ⟨i, hi⟩, hj⟩
  choose! T c hc hTc hcT hTbad using hbad
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := ℓ) (β := B)
    (by rw [Fintype.card_coe]; omega)
  set xs : ℓ → S := fun k => (f k).1
  have hxsB : ∀ k, xs k ∈ B := fun k => (f k).2
  set Tc : Finset ι := Finset.univ.biUnion fun k => (T (xs k))ᶜ
  have hTc_card : Tc.card ≤ L * e :=
    (Finset.card_biUnion_le_card_mul _ _ _ fun k _ => hTc _ (hxsB k)).trans_eq
      (by rw [Finset.card_univ])
  obtain ⟨cs, hcs_mem, -, hspan⟩ := exists_codewordSpan_of_isMDSGenerator G hG hdim MC U
    (Subtype.val_injective.comp f.injective) (fun k => hc _ (hxsB k)) (A₀ := Tcᶜ)
    fun k i hi => hcT _ (hxsB k) i ((by simpa [Tc] using hi : ∀ k, i ∈ T (xs k)) k)
  have hcw : ∀ x ∈ B, c x = ∑ j, G x j • cs j := fun x hx =>
    hspan x (c x) (hc x hx) (T x) (hcT x hx) <| by
      rw [Finset.compl_inter, compl_compl]
      exact ((Finset.card_union_le _ _).trans (Nat.add_le_add hTc_card (hTc x hx))).trans_lt
        (by omega)
  have hagree : ∀ x ∈ B, ∀ i ∈ T x, ∑ j, G x j • U j i = ∑ j, G x j • cs j i :=
    fun x hx i hi => by simp [hcT x hx i hi, hcw x hx, Finset.sum_apply]
  set E := Code.disagreementCols (fun i j => U j i) (fun i j => cs j i)
  set X : ι → Finset S :=
    fun i => Finset.univ.filter fun x => ∑ j, G x j • U j i = ∑ j, G x j • cs j i
  have hE_card : E.card < e + 1 :=
    (Code.hammingDist_eq_disagreementCols_card _ _).symm.trans_lt <|
      hammingDist_lt_of_isMDSGenerator G hG hdim U cs B (t := 1) (by omega)
        (fun x hx => (Code.closeToWord_iff_exists_possibleDisagreeCols _ _ _).mpr
          ⟨(T x)ᶜ, hTc x hx, fun i hi => hagree x hx i (Finset.notMem_compl.mp hi)⟩)
        (by rwa [one_mul])
  have hX_card : ∀ i ∈ E, (X i).card ≤ r := fun i hi =>
    card_filter_sum_smul_eq_le_of_isMDSGenerator G hG hdim (Code.mem_disagreementCols.mp hi)
  have hE_of_bad : ∀ x ∈ B, ∃ i ∈ T x, i ∈ E := fun x hx => by
    by_contra! hnone
    obtain ⟨j, hj⟩ := hTbad x hx
    exact hj ((mem_projectedCodeSubmod_iff MC (T x) _).mpr ⟨cs j, hcs_mem j, funext fun i =>
      congrFun (not_not.mp (mt Code.mem_disagreementCols.mpr (hnone i.1 i.2))) j⟩)
  have hα : B.card ≤ E.card * r :=
    (Finset.card_le_card fun x hx => by
      obtain ⟨i, hiT, hiE⟩ := hE_of_bad x hx
      exact Finset.mem_biUnion.mpr
        ⟨i, hiE, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree x hx i hiT⟩⟩).trans
      (Finset.card_biUnion_le_card_mul E X r hX_card)
  linarith [Nat.mul_le_mul_right r (Nat.lt_succ_iff.mp hE_card)]

/-- **Lemma 6.2 [BCGM25]** (with the corrected bound; see the module docstring). Every MDS
generator whose code has full dimension `ℓ ≥ 2` has mutual correlated agreement for every module
code `MC` at every radius `γ < δ_C / (ℓ + 1)`, with the `mdsMCAError` bound
`(⌊n·γ⌋ + 1)·(ℓ - 1) / |S|`. The slack `η` is a dummy: the unique-decoding branch of
`mdsMCAError` does not read it.

Stated pointwise in `γ` rather than as an `IsMCAGenerator`, which would demand a bound at every
radius; above `δ_C / (ℓ + 1)` that is the list-decoding regime of
`isMCAGenerator_of_isMDSGenerator`. The bound is the seed count
`card_filter_isMCA_le_of_isMDSGenerator`, converted to a probability by
`mcaError_le_of_exists_exceptional_set` with the set of bad seeds as the exceptional set. -/
lemma mcaError_le_mdsMCAError_of_lt {S : Type} [Nonempty S] [Fintype S] [SampleableType S]
    [DecidableEq F] [DecidableEq A] [Nonempty ι] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (hℓ : 2 ≤ Fintype.card ℓ) (MC : ModuleCode ι F A) (η : ℝ) (γ : I)
    (hγ : (γ : ℝ) < (Code.minRelHammingDistCode MC.carrier : ℝ) / (Fintype.card ℓ + 1)) :
    mcaError G MC γ ≤ (mdsMCAError MC (Fintype.card ℓ) (Fintype.card S) η γ : ENNReal) := by
  classical
  refine (mcaError_le_of_exists_exceptional_set G MC γ
    ((⌊(Fintype.card ι : ℝ) * γ⌋₊ + 1) * (Fintype.card ℓ - 1)) fun U =>
      ⟨Finset.univ.filter fun x => IsMCA G MC x U γ, ?_,
        fun x hx h => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩).trans_eq ?_
  · rw [mul_comm (Fintype.card ι : ℝ), ← Nat.cast_pred (by omega)]
    exact_mod_cast card_filter_isMCA_le_of_isMDSGenerator G hG hdim hℓ MC U γ.2.1 hγ
  · simp only [mdsMCAError, ite_eq_left hγ, mul_div_assoc]
    rfl

open Classical in
/-- Fix maximal agreement domains `T k` between the generated words `∑ j, G (xs k) j • U j` and
the code at `|ℓ|` distinct seeds `xs k`, with intersection `A₀`. At any seed `x`, a set `B` on
which the generated word lies in the projected code is contained in every maximal agreement
domain `Tx` of that word, provided both `A₀ ∩ B` and `A₀ ∩ Tx` miss fewer than `d_C` positions.

By `exists_codewordSpan_of_isMDSGenerator`, both large overlaps pin the respective codewords to
the same span codeword `∑ j, G x j • cs j`, and `Tx` is the exact agreement set of its codeword
(`LinearCode.IsMaxAgreementDomain.exists_codeword`). This is the step of [BCGM25] cited as "from
the proof of Lemma 6.4": with `x := xs k` and `Tx := T k` it is the maximality half of
`isMaxCADomain_inf_of_isMDSGenerator`, and with `B := A₀` it gives `A₀ ⊆ Tx`. -/
lemma subset_isMaxAgreementDomain_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {xs : ℓ → S} (hxs : Function.Injective xs)
    {T : ℓ → Finset ι}
    (hT : ∀ k, IsMaxAgreementDomain MC (fun i => ∑ j, G (xs k) j • U j i) (T k))
    {x : S} {Tx B : Finset ι}
    (hTx : IsMaxAgreementDomain MC (fun i => ∑ j, G x j • U j i) Tx)
    (hTxc : ((Finset.univ.inf T ∩ Tx)ᶜ).card < Code.minDist MC.carrier)
    (hB : projectedWord (fun i => ∑ j, G x j • U j i) B ∈ projectedCodeSubmod MC B)
    (hBc : ((Finset.univ.inf T ∩ B)ᶜ).card < Code.minDist MC.carrier) :
    B ⊆ Tx := by
  have hA₀sub : ∀ k, Finset.univ.inf T ⊆ T k := fun k => Finset.inf_le (Finset.mem_univ k)
  choose c hc hcT using fun k => (hT k).exists_codeword
  obtain ⟨cs, -, -, hspan⟩ := exists_codewordSpan_of_isMDSGenerator G hG hdim MC U hxs
    hc fun k i hi => (hcT k).1 i (hA₀sub k hi)
  obtain ⟨cx, hcx, hcxT, hcxmax⟩ := hTx.exists_codeword
  obtain ⟨c', hc', hc'B⟩ := (mem_projectedCodeSubmod_iff MC B _).mp hB
  have hagree : ∀ i ∈ B, ∑ j, G x j • U j i = c' i := fun i hi => congrFun hc'B ⟨i, hi⟩
  intro i hi
  exact hcxmax i <| (hagree i hi).trans <| congrFun
    ((hspan x c' hc' B hagree hBc).trans (hspan x cx hcx Tx hcxT hTxc).symm) i

open Classical in
/-- **Lemma 6.4 [BCGM25].** Let `G` be an MDS generator whose code has full dimension `|ℓ|`, and
fix maximal agreement domains `T k` between the generated words `∑ j, G (xs k) j • U j` and the
code, at `|ℓ|` distinct seeds `xs k`. If the domains intersect in all but fewer than `d_C`
positions, their intersection is a maximal CA domain between the family `U` and the code.

The intersection is a CA agreement set by `exists_codewordSpan_of_isMDSGenerator`
(Lemma 5.2 [BCGM25]): on it, each `U j` agrees with the span codeword `cs j`, and each domain's
codeword is `∑ j, G (xs k) j • cs j`. Maximality: on any larger CA agreement set `B`, each
generated word agrees with some codeword (`projectedCode_linearCombination`), so `B` lies in each
domain by `subset_isMaxAgreementDomain_of_isMDSGenerator`. -/
lemma isMaxCADomain_inf_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {xs : ℓ → S} (hxs : Function.Injective xs)
    {T : ℓ → Finset ι}
    (hT : ∀ k, IsMaxAgreementDomain MC (fun i => ∑ j, G (xs k) j • U j i) (T k))
    (hcard : ((Finset.univ.inf T)ᶜ).card < Code.minDist MC.carrier) :
    IsMaxCADomain MC U (Finset.univ.inf T) := by
  set A₀ := Finset.univ.inf T
  have hA₀sub : ∀ k, A₀ ⊆ T k := fun k => Finset.inf_le (Finset.mem_univ k)
  choose c hc hcT using fun k => (hT k).exists_codeword
  obtain ⟨cs, hcs_mem, hU_cs, -⟩ := exists_codewordSpan_of_isMDSGenerator G hG hdim MC U hxs
    hc fun k i hi => (hcT k).1 i (hA₀sub k hi)
  refine ⟨fun j => (mem_projectedCodeSubmod_iff MC A₀ _).mpr
      ⟨cs j, hcs_mem j, funext fun i => hU_cs j i.1 i.2⟩,
    fun B hB hA₀B => Finset.le_inf fun k _ => ?_⟩
  obtain ⟨c', hc', hc'B⟩ := projectedCode_linearCombination MC B U (G (xs k)) fun j =>
    (mem_projectedCodeSubmod_iff MC B _).mp (hB j)
  exact subset_isMaxAgreementDomain_of_isMDSGenerator G hG hdim MC U hxs hT (hT k)
    (by rwa [Finset.inter_eq_left.mpr (hA₀sub k)])
    ((mem_projectedCodeSubmod_iff MC B _).mpr ⟨c', hc', hc'B⟩)
    (by rwa [Finset.inter_eq_left.mpr hA₀B])

open Classical in
/-- **Lemma 6.5 [BCGM25].** Let `A₀` be a maximal CA domain between `U` and the code, missing
fewer than `d_C` positions, and let each `B t` be a maximal agreement domain of the generated
word at seed `xs t` containing `A₀`. Then any `|ℓ|` of the `B t` intersect exactly in `A₀`: the
intersection contains `A₀`, is a maximal CA domain by `isMaxCADomain_inf_of_isMDSGenerator`, and
`A₀`'s own maximality forces equality. -/
lemma inf_isMaxAgreementDomain_eq_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {τ : Type} {xs : τ → S}
    (hxs : Function.Injective xs) {A₀ : Finset ι} (hA₀ : IsMaxCADomain MC U A₀)
    (hcard : (A₀ᶜ).card < Code.minDist MC.carrier) {B : τ → Finset ι}
    (hB : ∀ t, IsMaxAgreementDomain MC (fun i => ∑ j, G (xs t) j • U j i) (B t))
    (hA₀B : ∀ t, A₀ ⊆ B t) {ks : ℓ → τ} (hks : Function.Injective ks) :
    Finset.univ.inf (fun k => B (ks k)) = A₀ := by
  have hsub : A₀ ⊆ Finset.univ.inf fun k => B (ks k) :=
    Finset.le_inf fun k _ => hA₀B (ks k)
  have hcard' : ((Finset.univ.inf fun k => B (ks k))ᶜ).card < Code.minDist MC.carrier :=
    lt_of_le_of_lt (Finset.card_le_card (Finset.compl_subset_compl.mpr hsub)) hcard
  have hmax := isMaxCADomain_inf_of_isMDSGenerator G hG hdim MC U (hxs.comp hks)
    (fun k => hB (ks k)) hcard'
  exact (Maximal.eq_of_le hA₀ hmax.1 hsub).symm

open Classical in
/-- In the situation of `inf_isMaxAgreementDomain_eq_of_isMDSGenerator`, the parts of the maximal
agreement domains `B t` outside `A₀` have total size at most `(|ℓ| - 1)·|A₀ᶜ|`. No position
outside `A₀` lies in `|ℓ|` of the `B t`, since those domains would intersect exactly in `A₀`;
double counting the incidences finishes.

This is the inequality `∑ᵢ |Bᵢ \ A| ≤ (ℓ - 1)·|⋃ᵢ Bᵢ \ A|` inside the proof of Lemma 6.6
[BCGM25]. A lower bound `m ≤ |B t \ A₀|` turns it into the seed count `m·|τ| ≤ (ℓ - 1)·|A₀ᶜ|`:
`m = 1` is Lemma 6.6 (`card_le_pred_mul_card_compl_of_isMDSGenerator`), and a larger `m` is the
modification of it used in the list-decoding count of Theorem 6.1. -/
lemma sum_card_sdiff_le_pred_mul_card_compl_of_isMDSGenerator {S : Type} [Nonempty S]
    [Fintype S] [DecidableEq F] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {τ : Type} [Fintype τ] {xs : τ → S}
    (hxs : Function.Injective xs) {A₀ : Finset ι} (hA₀ : IsMaxCADomain MC U A₀)
    (hcard : (A₀ᶜ).card < Code.minDist MC.carrier) {B : τ → Finset ι}
    (hB : ∀ t, IsMaxAgreementDomain MC (fun i => ∑ j, G (xs t) j • U j i) (B t))
    (hA₀B : ∀ t, A₀ ⊆ B t) :
    ∑ t, (B t \ A₀).card ≤ (Fintype.card ℓ - 1) * (A₀ᶜ).card := by
  have hd : ∀ p ∈ A₀ᶜ,
      ((Finset.univ : Finset τ).bipartiteBelow (fun t q => q ∈ B t) p).card
        ≤ Fintype.card ℓ - 1 := by
    intro p hp
    by_contra! hlt
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := ℓ)
      (β := (Finset.univ : Finset τ).bipartiteBelow (fun t q => q ∈ B t) p)
      (by rw [Fintype.card_coe]; omega)
    have heq := inf_isMaxAgreementDomain_eq_of_isMDSGenerator G hG hdim MC U hxs hA₀ hcard hB
      hA₀B (Subtype.val_injective.comp f.injective)
    have hpinf : p ∈ Finset.univ.inf fun k => B ((f k).1) :=
      Finset.mem_inf.mpr fun k _ => ((Finset.mem_bipartiteBelow (fun t q => q ∈ B t)).mp (f k).2).2
    exact Finset.mem_compl.mp hp (heq ▸ hpinf)
  have hsdiff : ∀ t, B t \ A₀ = (A₀ᶜ).bipartiteAbove (fun t q => q ∈ B t) t := fun t => by
    ext p
    simp [Finset.mem_bipartiteAbove, and_comm]
  simp_rw [hsdiff]
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow, mul_comm]
  exact Finset.sum_le_card_nsmul _ _ _ hd

open Classical in
/-- **Lemma 6.6 [BCGM25].** In the situation of
`inf_isMaxAgreementDomain_eq_of_isMDSGenerator`, if every maximal agreement domain `B t`
strictly contains `A₀`, then there are at most `(|ℓ| - 1)·|A₀ᶜ|` seeds: each `B t` reaches
outside `A₀` somewhere, so this is `sum_card_sdiff_le_pred_mul_card_compl_of_isMDSGenerator`
with every summand at least `1`. -/
lemma card_le_pred_mul_card_compl_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {τ : Type} [Fintype τ] {xs : τ → S}
    (hxs : Function.Injective xs) {A₀ : Finset ι} (hA₀ : IsMaxCADomain MC U A₀)
    (hcard : (A₀ᶜ).card < Code.minDist MC.carrier) {B : τ → Finset ι}
    (hB : ∀ t, IsMaxAgreementDomain MC (fun i => ∑ j, G (xs t) j • U j i) (B t))
    (hA₀B : ∀ t, A₀ ⊂ B t) :
    Fintype.card τ ≤ (Fintype.card ℓ - 1) * (A₀ᶜ).card := by
  refine le_trans ?_ (sum_card_sdiff_le_pred_mul_card_compl_of_isMDSGenerator G hG hdim MC U
    hxs hA₀ hcard hB fun t => (hA₀B t).subset)
  simpa using Finset.card_nsmul_le_sum Finset.univ (fun t => (B t \ A₀).card) 1
    fun t _ => Finset.card_pos.mpr (Finset.sdiff_nonempty.mpr (hA₀B t).not_subset)

omit [Fintype ℓ] in
open Classical in
/-- **Claim 6.7 [BCGM25].** Few maximal CA domains are large. Let `0 ≤ α ≤ 1` and `η > 0` with
`ρ + η ≤ α²`, and suppose the code's distance `d_C` satisfies `n - d_C ≤ n · ρ`. Then at most
`1 / η` maximal CA domains between `U` and the code have at least `n · α` positions; stated
division-free as `m · η ≤ 1`.

At the call site `α = (ρ_C + η) ^ (1 / ℓ)`, so that `n · α = n · (1 - γ_ℓ)`, and `ρ = ρ_C`.

Distinct maximal CA domains intersect in at most `n - d_C` positions
(`IsMaxCADomain.eq_of_card_compl_inter_lt_minDist`), so the Corrádi bound (Lemma 3.23 [BCGM25],
`Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le`) applies at the integer threshold
`a = ⌈n · α⌉`. The conversion to `m · η ≤ 1` uses only `n · α ≤ a ≤ n`, never an upper bound on
`a` in terms of `n · α`, so the rounding costs nothing. -/
lemma card_filter_isMaxCADomain_mul_le_one [Nonempty ι] (MC : ModuleCode ι F A)
    (U : ℓ → (ι → A)) {α ρ η : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hη : 0 < η)
    (hgap : ρ + η ≤ α * α)
    (hd : ((Fintype.card ι - Code.minDist MC.carrier : ℕ) : ℝ) ≤ Fintype.card ι * ρ) :
    ((Finset.univ.filter fun A₀ : Finset ι =>
        IsMaxCADomain MC U A₀ ∧ (Fintype.card ι : ℝ) * α ≤ A₀.card).card : ℝ) * η ≤ 1 := by
  set n := Fintype.card ι with hn_def
  set D := n - Code.minDist MC.carrier with hD_def
  set a := ⌈(n : ℝ) * α⌉₊ with ha_def
  set Fam := Finset.univ.filter fun A₀ : Finset ι =>
    IsMaxCADomain MC U A₀ ∧ (n : ℝ) * α ≤ A₀.card with hFam_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hαa : (n : ℝ) * α ≤ a := Nat.le_ceil _
  have han : a ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hanR : (a : ℝ) ≤ n := by exact_mod_cast han
  have hρα : ρ < α := by nlinarith
  have hDa : D ≤ a := by
    have : (D : ℝ) ≤ a := by nlinarith
    exact_mod_cast this
  have hpos : n * D < a * a := by
    have hnD : (n : ℝ) * D ≤ n * (n * ρ) := mul_le_mul_of_nonneg_left hd hnR.le
    have hsq : ((n : ℝ) * α) * ((n : ℝ) * α) ≤ a * a :=
      mul_le_mul hαa hαa (by positivity) (Nat.cast_nonneg a)
    have hng : (n : ℝ) * n * (ρ + η) ≤ n * n * (α * α) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have hnη : (0 : ℝ) < n * n * η := by positivity
    have : (n : ℝ) * D < a * a := by nlinarith
    exact_mod_cast this
  have hcorr := Finset.card_mul_sq_sub_card_mul_le_of_inter_card_le Fam id a D hDa hpos
    (fun A₀ hA₀ => Nat.ceil_le.mpr (Finset.mem_filter.mp hA₀).2.2)
    (fun A₁ h₁ A₂ h₂ hne => by
      by_contra! hlt
      refine hne (IsMaxCADomain.eq_of_card_compl_inter_lt_minDist
        (Finset.mem_filter.mp h₁).2.1 (Finset.mem_filter.mp h₂).2.1 ?_)
      have hle : (A₁ ∩ A₂).card ≤ n := Finset.card_le_univ _
      rw [Finset.card_compl]
      simp only [id] at hlt
      omega)
  -- convert the integer Corrádi bound to `m · η ≤ 1`, carrying `a` symbolically
  have h1 : ((a * a - n * D : ℕ) : ℝ) = (a : ℝ) * a - n * D := by
    push_cast [Nat.cast_sub hpos.le]; ring
  have h2 : ((a - D : ℕ) : ℝ) = (a : ℝ) - D := by push_cast [Nat.cast_sub hDa]; ring
  have hcorrR : (Fam.card : ℝ) * ((a : ℝ) * a - n * D) ≤ n * ((a : ℝ) - D) := by
    rw [← h1, ← h2]; exact_mod_cast hcorr
  have hden : (n : ℝ) ^ 2 * η ≤ (a : ℝ) * a - n * D := by
    nlinarith [mul_le_mul hαa hαa (by positivity : (0 : ℝ) ≤ (n : ℝ) * α) (Nat.cast_nonneg a)]
  have hnum : (n : ℝ) * ((a : ℝ) - D) ≤ (n : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    nlinarith
  have key : (Fam.card : ℝ) * ((n : ℝ) ^ 2 * η) ≤ (n : ℝ) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)) (hcorrR.trans hnum)
  have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  nlinarith [key, hsq]

open Classical in
/-- **Claim 6.8 [BCGM25].** Few seeds strictly extend a large maximal CA domain. Fix a maximal CA
domain `A₀` with at least `n · α` positions and fewer than `d_C` missing, and a set `Bad` of seeds
whose maximal agreement domains `T x` strictly contain `A₀`. Then
`|Bad| ≤ n · (1 - α) · (|ℓ| - 1)`.

At the call site `α = (ρ_C + η) ^ (1 / ℓ)`, so `n · (1 - α) = n · γ_ℓ`. The paper's "without loss of
generality `T` is a maximal agreement domain" is the hypothesis `hT`; the bound is Lemma 6.6
(`card_le_pred_mul_card_compl_of_isMDSGenerator`), with `|A₀ᶜ| ≤ n · (1 - α)`. -/
lemma card_le_of_ssubset_isMaxAgreementDomain_of_isMDSGenerator {S : Type} [Nonempty S]
    [Fintype S] [DecidableEq F] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (hℓ : 1 ≤ Fintype.card ℓ) (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {A₀ : Finset ι}
    (hA₀ : IsMaxCADomain MC U A₀) (hcard : (A₀ᶜ).card < Code.minDist MC.carrier) {α : ℝ}
    (hα : (Fintype.card ι : ℝ) * α ≤ A₀.card) (Bad : Finset S) (T : S → Finset ι)
    (hT : ∀ x ∈ Bad, IsMaxAgreementDomain MC (fun i => ∑ j, G x j • U j i) (T x))
    (hsub : ∀ x ∈ Bad, A₀ ⊂ T x) :
    (Bad.card : ℝ) ≤ Fintype.card ι * (1 - α) * (Fintype.card ℓ - 1) := by
  have h := card_le_pred_mul_card_compl_of_isMDSGenerator G hG hdim MC U
    (τ := {x // x ∈ Bad}) (xs := Subtype.val) Subtype.val_injective hA₀ hcard
    (B := fun t => T t.1) (fun t => hT t.1 t.2) (fun t => hsub t.1 t.2)
  rw [Fintype.card_coe] at h
  have hcompl : ((A₀ᶜ).card : ℝ) ≤ Fintype.card ι * (1 - α) := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ A₀)]
    linarith
  have hL : ((Fintype.card ℓ - 1 : ℕ) : ℝ) = (Fintype.card ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub hℓ, Nat.cast_one]
  have hR : (Bad.card : ℝ) ≤ ((Fintype.card ℓ - 1 : ℕ) : ℝ) * (A₀ᶜ).card := by exact_mod_cast h
  rw [hL] at hR
  have hL0 : (0 : ℝ) ≤ (Fintype.card ℓ : ℝ) - 1 := by rw [← hL]; positivity
  calc (Bad.card : ℝ) ≤ ((Fintype.card ℓ : ℝ) - 1) * (A₀ᶜ).card := hR
    _ ≤ ((Fintype.card ℓ : ℝ) - 1) * (Fintype.card ι * (1 - α)) :=
        mul_le_mul_of_nonneg_left hcompl hL0
    _ = Fintype.card ι * (1 - α) * (Fintype.card ℓ - 1) := by ring

open Classical in
/-- **Claim 6.9 [BCGM25].** Few seeds avoid every large maximal CA domain. Let `Bad` be seeds whose
maximal agreement domains `T x` have at least `n · β` positions but contain no maximal CA domain
with `n · α` positions. Then
`|Bad| ≤ max (2 · (|ℓ| - 1) / (η · (β - α))) (|ℓ| · (|ℓ| + 1) / η)`,
stated division-free as the disjunction of the two cleared bounds.

At the call site `β = (ρ_C + η) ^ (1 / (ℓ + 1))` and `α = (ρ_C + η) ^ (1 / ℓ)`, so that
`β ^ (ℓ + 1) = ρ_C + η` (`rpow_one_div_succ_pow`) and `α < β`
(`rpow_one_div_lt_rpow_one_div_succ`); `ρ = ρ_C`, with `n · (1 - ρ) ≤ d_C`.

Suppose both bounds fail. Since the average `(ℓ + 1)`-wise intersection of the `T x` exceeds
`n · ρ + n · η`, some `ℓ` distinct seeds `xs` have `A = ⋂ T (xs i)` meeting at least `η · |Bad| / 2`
of the `T x` in more than `n · ρ` positions
(`Finset.exists_injective_two_mul_card_filter_lt_card_inf_inter`). Then `A` misses fewer than `d_C`
positions, so it is a maximal CA domain (Lemma 6.4); it is contained in each of those `T x`
(`subset_isMaxAgreementDomain_of_isMDSGenerator`); and it has fewer than `n · α` positions,
since it lies in `T (xs i)`. So each such `T x` exceeds `A` by more than `n · (β - α)` positions,
and the Lemma 6.6 inequality `sum_card_sdiff_le_pred_mul_card_compl_of_isMDSGenerator` allows fewer
than `(ℓ - 1) / (β - α)` of them: a contradiction. -/
lemma card_mul_le_of_forall_not_subset_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] [Nonempty ι] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (hℓ : 2 ≤ Fintype.card ℓ) (MC : ModuleCode ι F A) (U : ℓ → (ι → A))
    {α β ρ η : ℝ} (hρ : 0 ≤ ρ) (hαβ : α < β) (hβ0 : 0 ≤ β)
    (hpow : ρ + η ≤ β ^ (Fintype.card ℓ + 1))
    (hd : (Fintype.card ι : ℝ) * (1 - ρ) ≤ Code.minDist MC.carrier)
    (Bad : Finset S) (T : S → Finset ι)
    (hT : ∀ x ∈ Bad, IsMaxAgreementDomain MC (fun i => ∑ j, G x j • U j i) (T x))
    (hlarge : ∀ x ∈ Bad, (Fintype.card ι : ℝ) * β ≤ (T x).card)
    (hB2 : ∀ x ∈ Bad, ∀ A₀ : Finset ι, IsMaxCADomain MC U A₀ →
      (Fintype.card ι : ℝ) * α ≤ A₀.card → ¬ A₀ ⊆ T x) :
    (Bad.card : ℝ) * η * (β - α) ≤ 2 * (Fintype.card ℓ - 1)
      ∨ (Bad.card : ℝ) * η ≤ Fintype.card ℓ * (Fintype.card ℓ + 1) := by
  by_contra! hcon
  obtain ⟨hN1, hN2⟩ := hcon
  set n := Fintype.card ι with hn_def
  set L := Fintype.card ℓ with hL_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hBadη : (0 : ℝ) < Bad.card * η := lt_of_le_of_lt (by positivity) hN2
  -- a dense intersection at `ℓ` distinct bad seeds
  have hchoose : (2 * L.choose 2 : ℝ) ≤ L * (L + 1) := by
    have h : 2 * L.choose 2 ≤ L * (L + 1) := by
      rw [Nat.choose_two_right]
      calc 2 * (L * (L - 1) / 2) ≤ L * (L - 1) := Nat.mul_div_le _ _
        _ ≤ L * (L + 1) := Nat.mul_le_mul_left _ (by omega)
    exact_mod_cast h
  obtain ⟨ys, hys, hgood⟩ := Finset.exists_injective_two_mul_card_filter_lt_card_inf_inter
    (β := {x // x ∈ Bad}) (κ := ℓ) (fun x => T x.1) (μ := n * β) (θ := n * ρ) (η := η)
    (by positivity) (by positivity) (fun x => hlarge x.1 x.2)
    (by
      calc (n : ℝ) ^ L * (n * ρ + n * η) = (n : ℝ) ^ (L + 1) * (ρ + η) := by ring
        _ ≤ (n : ℝ) ^ (L + 1) * β ^ (L + 1) := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((n : ℝ) * β) ^ (L + 1) := (mul_pow _ _ _).symm)
    (by rw [Fintype.card_coe]; linarith)
  rw [Fintype.card_coe] at hgood
  have hxs : Function.Injective fun i => (ys i).1 := Subtype.val_injective.comp hys
  have hTxs : ∀ i, IsMaxAgreementDomain MC (fun k => ∑ j, G (ys i).1 j • U j k) (T (ys i).1) :=
    fun i => hT _ (ys i).2
  -- a point count `n · ρ < |A ∩ T x|` means the overlap misses fewer than `d_C` positions
  have hmiss : ∀ X : Finset ι, (n : ℝ) * ρ < X.card → (Xᶜ).card < Code.minDist MC.carrier := by
    intro X hX
    have hXn : X.card ≤ n := Finset.card_le_univ X
    have : ((Xᶜ).card : ℝ) < Code.minDist MC.carrier := by
      rw [Finset.card_compl, Nat.cast_sub hXn]
      linarith
    exact_mod_cast this
  set Good := Finset.univ.filter fun x : {x // x ∈ Bad} =>
    (n : ℝ) * ρ < (((Finset.univ.inf fun i => T (ys i).1) ∩ T x.1).card : ℝ) with hGood_def
  have hGoodpos : 0 < Good.card := by
    have : (0 : ℝ) < Good.card := by linarith
    exact_mod_cast this
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hGoodpos
  -- the intersection is a maximal CA domain with fewer than `n · α` positions
  have hAcompl : ((Finset.univ.inf fun i => T (ys i).1)ᶜ).card < Code.minDist MC.carrier := by
    refine hmiss _ (lt_of_lt_of_le (Finset.mem_filter.mp hx₀).2 ?_)
    exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hAmax : IsMaxCADomain MC U (Finset.univ.inf fun i => T (ys i).1) :=
    isMaxCADomain_inf_of_isMDSGenerator G hG hdim MC U hxs hTxs hAcompl
  have hAsmall : ((Finset.univ.inf fun i => T (ys i).1).card : ℝ) < n * α := by
    by_contra! h
    have i₀ : ℓ := Classical.choice (Fintype.card_pos_iff.mp (by omega))
    exact hB2 _ (ys i₀).2 _ hAmax h (Finset.inf_le (Finset.mem_univ i₀))
  -- every dense seed's domain contains the intersection
  set Cnt := Bad.filter fun x => (Finset.univ.inf fun i => T (ys i).1) ⊆ T x with hCnt_def
  have hGoodCnt : Good.card ≤ Cnt.card := by
    refine Finset.card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_)
      (Subtype.val_injective.injOn)
    refine Finset.mem_filter.mpr ⟨x.2, ?_⟩
    exact subset_isMaxAgreementDomain_of_isMDSGenerator G hG hdim MC U hxs hTxs (hT x.1 x.2)
      (hmiss _ (Finset.mem_filter.mp hx).2)
      ((mem_projectedCodeSubmod_iff MC _ _).mpr <| projectedCode_linearCombination MC _ U
        (G x.1) fun j => (mem_projectedCodeSubmod_iff MC _ _).mp (hAmax.prop j))
      (by rwa [Finset.inter_self])
  -- the Lemma 6.6 inequality, with every excess at least `⌈n · β⌉ - |A|`
  have hwA : (Finset.univ.inf fun i => T (ys i).1).card ≤ ⌈(n : ℝ) * β⌉₊ := by
    have : ((Finset.univ.inf fun i => T (ys i).1).card : ℝ) ≤ ⌈(n : ℝ) * β⌉₊ :=
      hAsmall.le.trans ((mul_le_mul_of_nonneg_left hαβ.le hnR.le).trans (Nat.le_ceil _))
    exact_mod_cast this
  have hcnt : Fintype.card {x // x ∈ Cnt}
      * (⌈(n : ℝ) * β⌉₊ - (Finset.univ.inf fun i => T (ys i).1).card)
      ≤ (L - 1) * ((Finset.univ.inf fun i => T (ys i).1)ᶜ).card := by
    have hsum := sum_card_sdiff_le_pred_mul_card_compl_of_isMDSGenerator G hG hdim MC U
      (τ := {x // x ∈ Cnt}) (xs := Subtype.val) Subtype.val_injective hAmax hAcompl
      (B := fun t => T t.1) (fun t => hT t.1 (Finset.mem_filter.mp t.2).1)
      (fun t => (Finset.mem_filter.mp t.2).2)
    have hle := Finset.card_nsmul_le_sum (Finset.univ : Finset {x // x ∈ Cnt})
      (fun t => (T t.1 \ Finset.univ.inf fun i => T (ys i).1).card)
      (⌈(n : ℝ) * β⌉₊ - (Finset.univ.inf fun i => T (ys i).1).card)
      (fun t _ => (Nat.sub_le_sub_right
        (Nat.ceil_le.mpr (hlarge t.1 (Finset.mem_filter.mp t.2).1)) _).trans
        (Finset.le_card_sdiff _ _))
    rw [smul_eq_mul, Finset.card_univ] at hle
    exact hle.trans hsum
  rw [Fintype.card_coe] at hcnt
  -- conclude in the reals
  have hwR : (n : ℝ) * (β - α)
      ≤ ((⌈(n : ℝ) * β⌉₊ - (Finset.univ.inf fun i => T (ys i).1).card : ℕ) : ℝ) := by
    rw [Nat.cast_sub hwA]
    linarith [Nat.le_ceil ((n : ℝ) * β)]
  have hcomplR : (((Finset.univ.inf fun i => T (ys i).1)ᶜ).card : ℝ) ≤ n := by
    exact_mod_cast Finset.card_le_univ _
  have hL1 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hcntR : (Cnt.card : ℝ)
      * ((⌈(n : ℝ) * β⌉₊ - (Finset.univ.inf fun i => T (ys i).1).card : ℕ) : ℝ)
      ≤ ((L : ℝ) - 1) * ((Finset.univ.inf fun i => T (ys i).1)ᶜ).card := by
    rw [← hL1]; exact_mod_cast hcnt
  have hL0 : (0 : ℝ) ≤ (L : ℝ) - 1 := by rw [← hL1]; positivity
  have hCntβ : (Cnt.card : ℝ) * (β - α) ≤ (L : ℝ) - 1 := by
    have h1 : (Cnt.card : ℝ) * ((n : ℝ) * (β - α)) ≤ ((L : ℝ) - 1) * n :=
      (mul_le_mul_of_nonneg_left hwR (Nat.cast_nonneg _)).trans
        (hcntR.trans (mul_le_mul_of_nonneg_left hcomplR hL0))
    nlinarith
  have hGoodR : (Good.card : ℝ) ≤ Cnt.card := by exact_mod_cast hGoodCnt
  have hβα : (0 : ℝ) ≤ β - α := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hGoodR hβα]

open Classical in
/-- **The list-decoding seed count of Theorem 6.1 [BCGM25].** At a radius `γ ≤ 1 - β`, at most
`n · (1 - α) · (|ℓ| - 1) / η + max (2 · (|ℓ| - 1) / (η · (β - α))) (|ℓ| · (|ℓ| + 1) / η)`
seeds witness the MCA event for a fixed family `U`.

This is the body of the paper's proof of Theorem 6.1, at abstract thresholds; the theorem
instantiates `α = (ρ_C + η) ^ (1 / ℓ)` and `β = (ρ_C + η) ^ (1 / (ℓ + 1))`. Each bad seed's witness
set extends to a maximal agreement domain `T x` with at least `n · β` positions that is not a CA
agreement set. The bad seeds split by whether `T x` contains a maximal CA domain with `n · α`
positions:
* those that do (`B⁽¹⁾`) are covered by the at most `1 / η` such domains (Claim 6.7), each
  strictly contained in at most `n · (1 - α) · (|ℓ| - 1)` of the `T x` (Claim 6.8);
* those that do not (`B⁽²⁾`) are bounded by Claim 6.9. -/
lemma card_filter_isMCA_le_of_isMDSGenerator_of_le_one_sub {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] [Nonempty ι] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (hℓ : 2 ≤ Fintype.card ℓ) (MC : ModuleCode ι F A) (U : ℓ → (ι → A))
    {α β ρ η γ : ℝ} (hρ : 0 ≤ ρ) (hη : 0 < η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hαβ : α < β)
    (hβ0 : 0 ≤ β) (hgap : ρ + η ≤ α * α) (hpow : ρ + η ≤ β ^ (Fintype.card ℓ + 1))
    (hd : (Fintype.card ι : ℝ) * (1 - ρ) ≤ Code.minDist MC.carrier) (hγ : γ ≤ 1 - β) :
    ((Finset.univ.filter fun x => IsMCA G MC x U γ).card : ℝ)
      ≤ Fintype.card ι * (1 - α) * (Fintype.card ℓ - 1) / η
        + max (2 * (Fintype.card ℓ - 1) / (η * (β - α)))
            (Fintype.card ℓ * (Fintype.card ℓ + 1) / η) := by
  set n := Fintype.card ι with hn_def
  set L := Fintype.card ℓ with hL_def
  set Bad := Finset.univ.filter fun x => IsMCA G MC x U γ with hBad_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hρα : ρ < α := by nlinarith
  -- each bad seed has a large maximal agreement domain that is not a CA agreement set
  have hext : ∀ x ∈ Bad, ∃ T : Finset ι,
      IsMaxAgreementDomain MC (fun i => ∑ j, G x j • U j i) T ∧ (n : ℝ) * β ≤ T.card ∧
        ∃ j, projectedWord (U j) T ∉ projectedCodeSubmod MC T := by
    intro x hx
    obtain ⟨T₀, hT₀, hmem, j, hj⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨T, hT₀T, hTmax⟩ := exists_subset_isMaxAgreementDomain MC hmem
    refine ⟨T, hTmax, ?_, j, fun hjT => hj ?_⟩
    · have hcard : (T₀.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hT₀T
      have hβγ : (n : ℝ) * β ≤ n * (1 - γ) := mul_le_mul_of_nonneg_left (by linarith) hnR.le
      linarith
    · obtain ⟨c, hc, hcT⟩ := (mem_projectedCodeSubmod_iff MC T _).mp hjT
      exact (mem_projectedCodeSubmod_iff MC T₀ _).mpr
        ⟨c, hc, funext fun i => congrFun hcT ⟨i.1, hT₀T i.2⟩⟩
  choose! Tx hTmax hTlarge hTbad using hext
  -- split by whether the domain contains a large maximal CA domain
  set Large := Finset.univ.filter fun A₀ : Finset ι =>
    IsMaxCADomain MC U A₀ ∧ (n : ℝ) * α ≤ A₀.card with hLarge_def
  set B1 := Bad.filter fun x => ∃ A₀ ∈ Large, A₀ ⊆ Tx x with hB1_def
  set B2 := Bad.filter fun x => ¬ ∃ A₀ ∈ Large, A₀ ⊆ Tx x with hB2_def
  have hsplit : (Bad.card : ℝ) = B1.card + B2.card := by
    have := Finset.card_filter_add_card_filter_not (s := Bad) fun x => ∃ A₀ ∈ Large, A₀ ⊆ Tx x
    exact_mod_cast this.symm
  -- Claim 6.7: few large maximal CA domains
  have hd' : ((n - Code.minDist MC.carrier : ℕ) : ℝ) ≤ n * ρ := by
    rcases le_total (Code.minDist MC.carrier) n with h | h
    · rw [Nat.cast_sub h]; linarith
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]; positivity
  have hLarge : (Large.card : ℝ) * η ≤ 1 :=
    card_filter_isMaxCADomain_mul_le_one MC U hα0 hα1 hη hgap hd'
  -- Claim 6.8: each large domain is strictly contained in few seed domains
  have hK : (0 : ℝ) ≤ n * (1 - α) * (L - 1) :=
    mul_nonneg (mul_nonneg hnR.le (by linarith)) (by linarith)
  have hper : ∀ A₀ ∈ Large,
      ((Bad.filter fun x => A₀ ⊆ Tx x).card : ℝ) ≤ n * (1 - α) * (L - 1) := by
    intro A₀ hA₀
    obtain ⟨hAmax, hAlarge⟩ := (Finset.mem_filter.mp hA₀).2
    have hAcompl : (A₀ᶜ).card < Code.minDist MC.carrier := by
      have h1 : ((A₀ᶜ).card : ℝ) ≤ n * (1 - α) := by
        rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ _)]; linarith
      have h2 : (n : ℝ) * (1 - α) < n * (1 - ρ) := by nlinarith
      exact_mod_cast (h1.trans_lt h2).trans_le hd
    refine card_le_of_ssubset_isMaxAgreementDomain_of_isMDSGenerator G hG hdim (by omega) MC U
      hAmax hAcompl hAlarge _ Tx (fun x hx => hTmax x (Finset.mem_filter.mp hx).1) ?_
    intro x hx
    obtain ⟨hxBad, hsubx⟩ := Finset.mem_filter.mp hx
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubx, fun heq => ?_⟩
    obtain ⟨j, hj⟩ := hTbad x hxBad
    exact hj (heq ▸ hAmax.prop j)
  have hB1 : (B1.card : ℝ) ≤ Large.card * (n * (1 - α) * (L - 1)) := by
    have hsub : B1 ⊆ Large.biUnion fun A₀ => Bad.filter fun x => A₀ ⊆ Tx x := by
      intro x hx
      obtain ⟨hxBad, A₀, hA₀, hsubx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_biUnion.mpr ⟨A₀, hA₀, Finset.mem_filter.mpr ⟨hxBad, hsubx⟩⟩
    calc (B1.card : ℝ)
        ≤ ∑ A₀ ∈ Large, ((Bad.filter fun x => A₀ ⊆ Tx x).card : ℝ) := by
          exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ _A₀ ∈ Large, (n * (1 - α) * (L - 1) : ℝ) := Finset.sum_le_sum hper
      _ = Large.card * (n * (1 - α) * (L - 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hB1R : (B1.card : ℝ) ≤ n * (1 - α) * (L - 1) / η := by
    rw [le_div_iff₀ hη]
    nlinarith [mul_le_mul_of_nonneg_right hB1 hη.le, mul_le_mul_of_nonneg_right hLarge hK]
  -- Claim 6.9: the seeds avoiding every large domain
  have hB2 := card_mul_le_of_forall_not_subset_of_isMDSGenerator G hG hdim hℓ MC U hρ hαβ hβ0
    hpow hd B2 Tx (fun x hx => hTmax x (Finset.mem_filter.mp hx).1)
    (fun x hx => hTlarge x (Finset.mem_filter.mp hx).1)
    (fun x hx A₀ hAmax hAlarge hsubx => (Finset.mem_filter.mp hx).2
      ⟨A₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAmax, hAlarge⟩, hsubx⟩)
  have hB2R : (B2.card : ℝ) ≤ max (2 * (L - 1) / (η * (β - α))) (L * (L + 1) / η) := by
    have hβα : 0 < β - α := by linarith
    rcases hB2 with h | h
    · refine le_max_of_le_left ?_
      rw [le_div_iff₀ (by positivity)]; linarith
    · refine le_max_of_le_right ?_
      rw [le_div_iff₀ hη]; linarith
  rw [hsplit]
  linarith

/-- Every MDS generator whose code has full dimension `ℓ ≥ 2` has MCA for every module code `MC`,
with error `mdsMCAError MC ℓ |S| η`, for every slack `0 < η < 1`. The generator-matrix hypotheses
constrain `G` over the base field only; the tested code's alphabet is any `F`-module.
Theorem 6.1 [BCGM25].

The proof splits on the three branches of `mdsMCAError`. Below `δ_C / (ℓ + 1)` it is Lemma 6.2
(`mcaError_le_mdsMCAError_of_lt`). Up to `1 - (ρ_C + η) ^ (1 / (ℓ + 1))` it is the seed count
`card_filter_isMCA_le_of_isMDSGenerator_of_le_one_sub`, at the thresholds
`α = (ρ_C + η) ^ (1 / ℓ)` and `β = (ρ_C + η) ^ (1 / (ℓ + 1))`; that branch forces `ρ_C + η < 1`
(`one_sub_add_lt_one_of_le_one_sub_rpow`), so the margin `β - α` is positive there. Beyond it the
bound is `1`. -/
theorem isMCAGenerator_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [SampleableType S] [DecidableEq F] [DecidableEq A] [Nonempty ι]
    (G : Generator S ℓ F)
    (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (η : ℝ) (hη : 0 < η ∧ η < 1) (hℓ : 2 ≤ Fintype.card ℓ)
    (MC : ModuleCode ι F A) :
  IsMCAGenerator G (mdsMCAError MC (Fintype.card ℓ) (Fintype.card S) η) MC := by
  intro γ
  by_cases hγ : (γ : ℝ) < (Code.minRelHammingDistCode MC.carrier : ℝ) / (Fintype.card ℓ + 1)
  · exact mcaError_le_mdsMCAError_of_lt G hG hdim hℓ MC η γ hγ
  simp only [mdsMCAError]
  split_ifs with hup
  · -- the list-decoding branch: instantiate the thresholds of the seed count
    have hδq := congrArg (Rat.cast (K := ℝ))
      (Code.minDist_div_card_eq_minRelHammingDistCode MC.carrier)
    push_cast at hδq
    have hδ1 : (Code.minRelHammingDistCode MC.carrier : ℝ) ≤ 1 := by
      exact_mod_cast Code.minRelHammingDistCode_le_one
    set δ : ℝ := (Code.minRelHammingDistCode MC.carrier : ℝ) with hδ_def
    set L := Fintype.card ℓ with hL_def
    set n := Fintype.card ι with hn_def
    set ρ : ℝ := 1 - δ with hρ_def
    set α : ℝ := (ρ + η) ^ (1 / L : ℝ) with hα_def
    set β : ℝ := (ρ + η) ^ (1 / (L + 1) : ℝ) with hβ_def
    have hnR : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
    have hρ : 0 ≤ ρ := by linarith
    have hlt1 : ρ + η < 1 :=
      one_sub_add_lt_one_of_le_one_sub_rpow δ η γ L hη.1 γ.2.1 (not_lt.mp hγ) hup
    have hb : 0 < ρ + η := by linarith [hη.1]
    have hα0 : 0 ≤ α := Real.rpow_nonneg hb.le _
    have hα1 : α ≤ 1 := Real.rpow_le_one hb.le hlt1.le (by positivity)
    have hαβ : α < β := rpow_one_div_lt_rpow_one_div_succ ρ η L hρ hη.1 hlt1 (by omega)
    have hβ0 : 0 ≤ β := Real.rpow_nonneg hb.le _
    have hgap : ρ + η ≤ α * α := by
      have hαα : α * α = (ρ + η) ^ (2 / L : ℝ) := by
        rw [hα_def, ← Real.rpow_add hb]; congr 1; ring
      rw [hαα]; exact le_rpow_two_div ρ η L hρ hη.1 hlt1.le hℓ
    have hpow : ρ + η ≤ β ^ (L + 1) := (rpow_one_div_succ_pow (ρ + η) L hb.le).symm.le
    have hd : (n : ℝ) * (1 - ρ) ≤ Code.minDist MC.carrier := by
      rw [hρ_def, sub_sub_cancel, ← hδq, mul_div_cancel₀ _ hnR.ne']
    refine (mcaError_le_of_exists_exceptional_set G MC γ
      (n * (1 - α) * (L - 1) / η + max (2 * (L - 1) / (η * (β - α))) (L * (L + 1) / η))
      fun U => ⟨_, card_filter_isMCA_le_of_isMDSGenerator_of_le_one_sub G hG hdim hℓ MC U hρ
        hη.1 hα0 hα1 hαβ hβ0 hgap hpow (by convert hd) hup,
        fun x hx h => hx (by simpa using h)⟩).trans (le_of_eq ?_)
    unfold ENNReal.ofReal
    congr 2
    rw [add_div, ← max_div_div_right (Nat.cast_nonneg _)]
    simp only [div_div]
    congr 1
    ring
  · -- beyond the list-decoding radius the bound is trivial
    simpa using mcaError_le_one G MC γ

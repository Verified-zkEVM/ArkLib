/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
public import ArkLib.Data.CodingTheory.ProximityGenerator.ExceptionalSet

/-!
# Mutual correlated agreement for MDS generators

Every MDS generator whose code has full dimension `ℓ ≥ 2` has mutual correlated agreement for
every module code, with error `mdsMCAError`. The unique-decoding regime is proved
(`isMCAGenerator_of_isMDSGenerator_uniqueDecoding`); the list-decoding regime is open.

## Main statements

* `mdsMCAError` — the MCA error function of an MDS generator, with `mdsMCAError_congr` showing it
  depends on the code only through its block length and relative distance.
* `mdsMCAError_uniqueDecoding` — its unique-decoding regime alone, agreeing with `mdsMCAError`
  below the radius `δ_C / (ℓ + 1)` (`mdsMCAError_eq_uniqueDecoding`).
* `card_filter_isMCA_le_of_isMDSGenerator` — the seed count behind the unique-decoding regime: at
  most `(⌊n·γ⌋ + 1)·(ℓ - 1)` seeds witness the MCA event for a fixed word family.
* `isMCAGenerator_of_isMDSGenerator_uniqueDecoding` — MCA for MDS generators in the
  unique-decoding regime (Lemma 6.2 [BCGM25], with the corrected bound below).
* `isMCAGenerator_of_isMDSGenerator` — MCA for MDS generators (sorried in the list-decoding
  regime).

## Departure from [BCGM25]

Lemma 6.2 of [BCGM25] prints the unique-decoding error as `max{n·γ, 1}·(ℓ - 1) / |S|`. That
bound is false whenever `1 ≤ ⌊n·γ⌋`: for the affine line generator `x ↦ (1, x)` and words
`u₁ = η₁`, `u₂ = η₂` supported on a common set of `⌊n·γ⌋ + 1` positions with pairwise distinct
ratios `η₁[i] / η₂[i]`, each of the `⌊n·γ⌋ + 1` seeds `x = -η₁[i] / η₂[i]` cancels position
`i` and witnesses the MCA event at radius `γ`, exceeding the printed `n·γ·(ℓ - 1) = ⌊n·γ⌋` when
`n·γ` is an integer. The error is therefore stated with `⌊n·γ⌋ + 1` in place of `max{n·γ, 1}`;
the two agree below `1/n`, and the corrected bound is attained by the example above. The paper's
argument, which the proof here follows, yields exactly this count: its step "`|T̃| > n·(1 - γ)`"
only follows in the weak form `n - |T̃| ≤ ⌊n·γ⌋`.

The correspondence to [BCGM25]'s numbered statements is in
`docs/kb/audits/bcgm25-mca-generators.md`.

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
bound `1` beyond. The unique-decoding regime replaces the paper's `max{n·γ, 1}` by `⌊n·γ⌋ + 1`;
see the module docstring.

Valued in `ℝ≥0` to match `IsMCAGenerator`, clamping the underlying real expression at `0` by
`Real.toNNReal`. The clamp is not lossy for the intended parameter range — the expression is a
bound on a probability, and is nonnegative wherever `0 < η < 1` and `2 ≤ ℓ` hold. -/
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

/-- The unique-decoding regime of `mdsMCAError`: the MCA error function of an MDS generator with
output size `ℓ` and `s` seeds, for a module code `MC`, that keeps the unique-decoding bound
`(⌊n·γ⌋ + 1)·(ℓ - 1) / s` below `δ_C / (ℓ + 1)` and is the trivial bound `1` beyond. Here
`n = |ι|` is the block length and `δ_C` the relative distance of `MC`.

It takes no slack parameter, since neither branch depends on one. Below the radius it agrees with
`mdsMCAError` (`mdsMCAError_eq_uniqueDecoding`). Valued in `ℝ≥0` to match `IsMCAGenerator`,
clamping the underlying real expression at `0` by `Real.toNNReal`. -/
noncomputable def mdsMCAError_uniqueDecoding [DecidableEq F] [DecidableEq A] [Nonempty ι]
    (MC : ModuleCode ι F A) (ℓ s : ℕ) : I → ℝ≥0 :=
  letI n : ℝ := Fintype.card ι
  letI δ_C : ℝ := (Code.minRelHammingDistCode (MC.carrier) : ℝ)
  fun γ =>
    Real.toNNReal <|
      if γ < (δ_C / (ℓ + 1) : ℝ) then
        letI m' : ℝ := ⌊n * γ⌋₊ + 1
        m' * ((ℓ - 1) / s : ℝ)
      else
        1

/-- Below the unique-decoding radius `δ_C / (ℓ + 1)`, `mdsMCAError` agrees with
`mdsMCAError_uniqueDecoding`, at every slack `η`. -/
lemma mdsMCAError_eq_uniqueDecoding [DecidableEq F] [DecidableEq A] [Nonempty ι]
    (MC : ModuleCode ι F A) (ℓ s : ℕ) (η : ℝ) (γ : I)
    (hγ : (γ : ℝ) < (Code.minRelHammingDistCode MC.carrier : ℝ) / (ℓ + 1)) :
    mdsMCAError MC ℓ s η γ = mdsMCAError_uniqueDecoding MC ℓ s γ := by
  simp only [mdsMCAError, mdsMCAError_uniqueDecoding, if_pos hγ]

/-- `mdsMCAError` reads the code only through the block length `ι` and the relative distance
`δᵣ`: two module codes over the same index set with equal `δᵣ` get the same error function,
regardless of their alphabets. In particular the error is unchanged under interleaving
(`Code.minRelHammingDistCode_moduleInterleavedCode`), which is what lets
`isMCAGenerator_of_isMDSGenerator` feed the interleaved-hypothesis tensor lemma. -/
lemma mdsMCAError_congr [DecidableEq F] [Nonempty ι] {A' : Type} [DecidableEq A]
    [AddCommMonoid A'] [Module F A'] [DecidableEq A']
    (MC : ModuleCode ι F A) (MC' : ModuleCode ι F A') (ℓ s : ℕ) (η : ℝ)
    (hδ : Code.minRelHammingDistCode MC'.carrier = Code.minRelHammingDistCode MC.carrier) :
    mdsMCAError MC' ℓ s η = mdsMCAError MC ℓ s η := by
  unfold mdsMCAError
  rw [hδ]

/-! ## The MDS property of the generator

An MDS generator with `C_G` of dimension `|ℓ|` is zero-evading with error `(|ℓ| - 1) / |S|`
(Lemma 3.13 [BCGM25]), and any `|ℓ|` of its rows form an invertible matrix (Lemma 3.6 [BCGM25]).
The zero-evading bound is first proved at the field, where it is the distance of `C_G`, and then
transported to any module alphabet through the invertible matrices. -/

/-- A nonzero `v : ℓ → F` is orthogonal to `G x` for at most `|ℓ| - 1` seeds `x`: the codeword
`x ↦ G x ⬝ᵥ v` of `C_G` is nonzero, since `C_G` has dimension `|ℓ|`, so its weight is at least the
MDS distance `|S| - |ℓ| + 1`. -/
lemma card_filter_dotProduct_eq_zero_le_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    {v : ℓ → F} (hv : v ≠ 0) :
    (Finset.univ.filter fun x => G x ⬝ᵥ v = 0).card ≤ Fintype.card ℓ - 1 := by
  have hc_mem : (M_G G).mulVec v ∈ LinearCode.fromColGenMat (M_G G) := ⟨v, rfl⟩
  -- `dim C_G = |ℓ|` makes `v ↦ (M_G G).mulVec v` injective, so the codeword is nonzero
  have hc_ne : (M_G G).mulVec v ≠ 0 := by
    intro hc0
    have hker : LinearMap.ker (M_G G).mulVecLin = ⊥ := by
      have h := LinearMap.finrank_range_add_finrank_ker (M_G G).mulVecLin
      have hr : Module.finrank F (LinearMap.range (M_G G).mulVecLin) = Fintype.card ℓ := hdim
      rw [Module.finrank_fintype_fun_eq_card, hr] at h
      exact Submodule.finrank_eq_zero.mp (by omega)
    exact hv (LinearMap.ker_eq_bot.mp hker (by simpa using hc0))
  have hℓS : Fintype.card ℓ ≤ Fintype.card S := by
    have h := Submodule.finrank_le (LinearCode.fromColGenMat (M_G G))
    rw [Module.finrank_fintype_fun_eq_card] at h
    exact hdim ▸ h
  -- the MDS distance bounds the weight of the nonzero codeword
  have hdist : Code.dist (LinearCode.fromColGenMat (M_G G)).carrier
      = Fintype.card S - Fintype.card ℓ + 1 := by
    have h : Code.dist (LinearCode.fromColGenMat (M_G G)).carrier
        = LinearCode.length (LinearCode.fromColGenMat (M_G G))
          - LinearCode.dim (LinearCode.fromColGenMat (M_G G)) + 1 := hG
    rw [h, hdim]
    rfl
  have hnorm : Fintype.card S - Fintype.card ℓ + 1 ≤ hammingNorm ((M_G G).mulVec v) := by
    by_contra hlt
    push Not at hlt
    refine hc_ne (Code.eq_of_lt_dist (C := (LinearCode.fromColGenMat (M_G G)).carrier) hc_mem
      (Submodule.zero_mem _) ?_)
    rwa [hammingDist_zero_right, hdist]
  -- the zeros and the support of the codeword partition the seeds
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
    (fun x => G x ⬝ᵥ v = 0)
  have hnorm_eq : hammingNorm ((M_G G).mulVec v)
      = (Finset.univ.filter fun x => ¬ G x ⬝ᵥ v = 0).card := by
    unfold hammingNorm
    rfl
  rw [Finset.card_univ] at hsplit
  omega

/-- Any `|ℓ|` distinct rows of the generator matrix of an MDS generator with `C_G` of dimension
`|ℓ|` form an invertible matrix: a vector in the kernel would give a codeword of `C_G` vanishing
at `|ℓ|` seeds. -/
lemma isUnit_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq ℓ] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    {xs : ℓ → S} (hxs : Function.Injective xs) :
    IsUnit (Matrix.of fun k j => G (xs k) j) := by
  refine Matrix.mulVec_injective_iff_isUnit.mp fun v w hvw => ?_
  by_contra hne
  obtain ⟨k₀, -⟩ := Function.ne_iff.mp hne
  have hz : ∀ k, G (xs k) ⬝ᵥ (v - w) = 0 := fun k => by
    have h := congrFun (show (Matrix.of fun k j => G (xs k) j).mulVec (v - w) = 0 by
      rw [Matrix.mulVec_sub, hvw, sub_self]) k
    simpa [Matrix.mulVec] using h
  have hsub : Finset.univ.map ⟨xs, hxs⟩ ⊆ Finset.univ.filter fun x => G x ⬝ᵥ (v - w) = 0 := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz k⟩
  have h₁ := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_univ] at h₁
  have h₂ := card_filter_dotProduct_eq_zero_le_of_isMDSGenerator G hG hdim (sub_ne_zero.mpr hne)
  have hpos : 0 < Fintype.card ℓ := Fintype.card_pos_iff.mpr ⟨k₀⟩
  omega

/-- Combining a module-valued family `v` against the rows of `M` and then against the rows of a
left inverse `N` of `M` recovers `v`: this is `N * M = 1` acting on `ℓ → A`. -/
lemma sum_smul_sum_smul_eq_of_mul_eq_one [DecidableEq ℓ] {N M : Matrix ℓ ℓ F} (h : N * M = 1)
    (v : ℓ → A) (j : ℓ) : ∑ k, N j k • ∑ j', M k j' • v j' = v j := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply]

/-- The module-valued zero-evading bound of an MDS generator: two distinct families `v w : ℓ → A`
have equal combinations `∑ j, G x j • v j = ∑ j, G x j • w j` for at most `|ℓ| - 1` seeds `x`,
since any `|ℓ|` seeds give an invertible matrix through which `v` and `w` are recovered from the
combinations. -/
lemma card_filter_sum_smul_eq_le_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F] [DecidableEq A] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    {v w : ℓ → A} (hvw : v ≠ w) :
    (Finset.univ.filter fun x => ∑ j, G x j • v j = ∑ j, G x j • w j).card
      ≤ Fintype.card ℓ - 1 := by
  classical
  by_contra hlt
  push Not at hlt
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

/-! ## The unique-decoding count

For `γ < δ_C / (|ℓ| + 1)` and a fixed family `U`, at most `(⌊n·γ⌋ + 1)·(|ℓ| - 1)` seeds witness
the MCA event. The argument is that of Lemma 6.2 [BCGM25]. Writing `e := ⌊n·γ⌋` and `B` for the
set of bad seeds, suppose `|B| > (e + 1)(|ℓ| - 1)`. Then `|B| ≥ |ℓ|`, so `|ℓ|` bad seeds give an
invertible matrix `M` and the family `U` is recovered from their combinations; on the common
agreement set of those seeds each `U j` agrees with a codeword `c*_j`. For every bad seed `x`, the
codeword close to its combination is `∑ j, G x j • c*_j`, by unique decoding: the two agree off
at most `(|ℓ| + 1)·e < d_C` positions. The bad seed then has to cancel some position `i` where
`U` and `c*` differ, i.e. `∑ j, G x j • U j i = ∑ j, G x j • c*_j i`, which for fixed `i` happens
for at most `|ℓ| - 1` seeds; so `|B| ≤ |E|·(|ℓ| - 1)` for `E` the set of such positions.
Conversely every bad seed fails to cancel at most `e` positions, so double counting gives
`|E|·(|B| - (|ℓ| - 1)) ≤ |B|·e`. Together, `|B| ≤ (e + 1)(|ℓ| - 1)`. -/

open Classical in
/-- **The unique-decoding seed count** (Lemma 6.2 [BCGM25], corrected). For `γ < δ_C / (|ℓ| + 1)`
and any family `U`, at most `(⌊n·γ⌋ + 1)·(|ℓ| - 1)` seeds `x` satisfy the MCA event
`IsMCA G MC x U γ`. -/
lemma card_filter_isMCA_le_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq A] [Nonempty ι] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (hℓ : 2 ≤ Fintype.card ℓ) (MC : ModuleCode ι F A) (U : ℓ → (ι → A)) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < (Code.minRelHammingDistCode MC.carrier : ℝ) / (Fintype.card ℓ + 1)) :
    (Finset.univ.filter fun x => IsMCA G MC x U γ).card
      ≤ (⌊γ * Fintype.card ι⌋₊ + 1) * (Fintype.card ℓ - 1) := by
  classical
  set n := Fintype.card ι with hn
  set L := Fintype.card ℓ with hL
  set e := ⌊γ * n⌋₊ with he
  set B := Finset.univ.filter fun x => IsMCA G MC x U γ with hB
  -- the combination of `U` at the seed `x`
  set u : S → ι → A := fun x i => ∑ j, G x j • U j i with hu
  -- the unique-decoding budget `(L + 1) e < d_C`
  have hd : (L + 1) * e < Code.minDist MC.carrier := by
    have hδ : (Code.minRelHammingDistCode MC.carrier : ℝ) = (Code.minDist MC.carrier : ℝ) / n := by
      have h := Code.minDist_div_card_eq_minRelHammingDistCode MC.carrier
      have h' := congrArg (fun q : ℚ => (q : ℝ)) h
      push_cast at h'
      exact h'.symm
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
    have he_le : (e : ℝ) ≤ γ * n := Nat.floor_le (by positivity)
    rw [hδ, div_div, lt_div_iff₀ (by positivity)] at hγ
    have : ((L + 1 : ℕ) : ℝ) * e < Code.minDist MC.carrier := by
      push_cast
      nlinarith
    exact_mod_cast this
  by_contra hlt
  push Not at hlt
  -- the data of the bad event at each bad seed: agreement set, codeword, bad index
  have hbad : ∀ x ∈ B, ∃ T : Finset ι, (T.card : ℝ) ≥ n * (1 - γ) ∧
      projectedWord (u x) T ∈ projectedCodeSubmod MC T ∧
      ∃ j, projectedWord (U j) T ∉ projectedCodeSubmod MC T :=
    fun x hx => (Finset.mem_filter.mp hx).2
  choose! T hTcard hTmem hTbad using hbad
  have hTc : ∀ x ∈ B, (T x)ᶜ.card ≤ e := fun x hx => by
    rw [Finset.card_compl]
    exact (mul_one_sub_le_card_iff_sub_card_le_floor (T x) hγ0).mp (hTcard x hx)
  have hTmem' : ∀ x ∈ B, ∃ c ∈ MC, ∀ i ∈ T x, u x i = c i := fun x hx => by
    obtain ⟨c, hc, hcT⟩ := (mem_projectedCodeSubmod_iff MC (T x) _).mp (hTmem x hx)
    exact ⟨c, hc, fun i hi => congrFun hcT ⟨i, hi⟩⟩
  choose! c hc hcT using hTmem'
  -- `L` distinct bad seeds, and the inverse of the matrix of their generator rows
  have hbk : L - 1 < B.card :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left (L - 1) (Nat.succ_pos e) : L - 1 ≤ (e + 1) * (L - 1)) hlt
  have hLB : L ≤ B.card := by omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := ℓ) (β := B)
    (by rw [Fintype.card_coe]; exact hLB)
  set xs : ℓ → S := fun k => (f k).1 with hxs
  have hxsB : ∀ k, xs k ∈ B := fun k => (f k).2
  have hxsinj : Function.Injective xs := Subtype.val_injective.comp f.injective
  set M : Matrix ℓ ℓ F := Matrix.of fun k j => G (xs k) j with hM
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M
    ((Matrix.isUnit_iff_isUnit_det M).mp (isUnit_of_isMDSGenerator G hG hdim hxsinj))
  -- the codewords `c*` solved from the chosen seeds, and `U` recovered from their combinations
  set cs : ℓ → ι → A := fun j => ∑ k, M⁻¹ j k • c (xs k) with hcs
  have hcs_mem : ∀ j, cs j ∈ MC := fun j =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hc _ (hxsB k))
  have hcs_apply : ∀ j i, cs j i = ∑ k, M⁻¹ j k • c (xs k) i := fun j i => by
    simp [hcs, Finset.sum_apply]
  have hU_eq : ∀ j i, U j i = ∑ k, M⁻¹ j k • u (xs k) i := fun j i =>
    (sum_smul_sum_smul_eq_of_mul_eq_one hNM (fun j => U j i) j).symm
  -- positions outside the common agreement set of the chosen seeds
  set Tc : Finset ι := Finset.univ.biUnion fun k => (T (xs k))ᶜ with hTc_def
  have hTc_card : Tc.card ≤ L * e := by
    refine (Finset.card_biUnion_le_card_mul _ _ _ fun k _ => hTc _ (hxsB k)).trans ?_
    rw [Finset.card_univ]
  have hU_cs : ∀ i, i ∉ Tc → ∀ j, U j i = cs j i := fun i hi j => by
    rw [hU_eq, hcs_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine hcT _ (hxsB k) i ?_
    by_contra h
    exact hi (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_compl.mpr h⟩)
  -- the combination of `c*` at the seed `x`
  set w : S → ι → A := fun x => ∑ j, G x j • cs j with hw
  have hw_mem : ∀ x, w x ∈ MC := fun x =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs_mem j)
  have hw_apply : ∀ x i, w x i = ∑ j, G x j • cs j i := fun x i => by
    simp [hw, Finset.sum_apply]
  -- unique decoding: the codeword close to `u x` is `w x`
  have hcw : ∀ x ∈ B, c x = w x := fun x hx => by
    refine Code.eq_of_disagreementCols_subset_of_card_lt_minDist (hc x hx) (hw_mem x)
      ((T x)ᶜ ∪ Tc) ?_ ?_
    · intro i hi
      rw [Code.mem_disagreementCols] at hi
      by_contra hcontra
      rw [Finset.mem_union, not_or, Finset.mem_compl, not_not] at hcontra
      apply hi
      rw [← hcT x hx i hcontra.1, hw_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [hU_cs i hcontra.2 j]
    · calc ((T x)ᶜ ∪ Tc).card ≤ (T x)ᶜ.card + Tc.card := Finset.card_union_le _ _
        _ ≤ e + L * e := Nat.add_le_add (hTc x hx) hTc_card
        _ = (L + 1) * e := by ring
        _ < _ := hd
  -- a bad seed agrees with `w x` at position `i` iff it cancels the difference of `U` and `c*`
  have hagree : ∀ x ∈ B, ∀ i ∈ T x, ∑ j, G x j • U j i = ∑ j, G x j • cs j i := fun x hx i hi => by
    have h := hcT x hx i hi
    rwa [hcw x hx, hw_apply] at h
  -- the positions where `U` and `c*` differ, and the seeds cancelling each of them
  set E := Finset.univ.filter fun i => ∃ j, U j i ≠ cs j i with hE
  set X : ι → Finset S :=
    fun i => Finset.univ.filter fun x => ∑ j, G x j • U j i = ∑ j, G x j • cs j i with hX
  have hX_card : ∀ i ∈ E, (X i).card ≤ L - 1 := fun i hi => by
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
    exact card_filter_sum_smul_eq_le_of_isMDSGenerator G hG hdim (v := fun j => U j i)
      (w := fun j => cs j i) (Function.ne_iff.mpr ⟨j, hj⟩)
  -- every bad seed cancels some differing position
  have hα : B.card ≤ E.card * (L - 1) := by
    refine (Finset.card_le_card ?_).trans (Finset.card_biUnion_le_card_mul E X (L - 1) hX_card)
    intro x hx
    obtain ⟨j, hj⟩ := hTbad x hx
    have hiE : ∃ i ∈ T x, i ∈ E := by
      by_contra hnone
      push Not at hnone
      apply hj
      have hUcs : projectedWord (U j) (T x) = projectedWord (cs j) (T x) := by
        funext ⟨i, hi⟩
        have h := hnone i hi
        simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_not] at h
        exact h j
      rw [hUcs, mem_projectedCodeSubmod_iff]
      exact ⟨cs j, hcs_mem j, rfl⟩
    obtain ⟨i, hiT, hiE⟩ := hiE
    exact Finset.mem_biUnion.mpr
      ⟨i, hiE, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree x hx i hiT⟩⟩
  -- every bad seed fails to cancel at most `e` positions: double counting
  have hβ : E.card * B.card ≤ E.card * (L - 1) + B.card * e := by
    have h₁ : ∀ i ∈ E, B.card ≤ (L - 1) + (B.filter fun x => x ∉ X i).card := fun i hi => by
      calc B.card = (B.filter fun x => x ∈ X i).card + (B.filter fun x => x ∉ X i).card :=
            (Finset.card_filter_add_card_filter_not _).symm
        _ ≤ (X i).card + (B.filter fun x => x ∉ X i).card :=
            Nat.add_le_add_right (Finset.card_le_card fun x hx => (Finset.mem_filter.mp hx).2) _
        _ ≤ (L - 1) + (B.filter fun x => x ∉ X i).card := Nat.add_le_add_right (hX_card i hi) _
    have h₂ : ∀ x ∈ B, (E.filter fun i => x ∉ X i).card ≤ e := fun x hx => by
      refine (Finset.card_le_card ?_).trans (hTc x hx)
      intro i hi
      obtain ⟨-, hiX⟩ := Finset.mem_filter.mp hi
      rw [Finset.mem_compl]
      exact fun hiT => hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree x hx i hiT⟩)
    have hswap : ∑ i ∈ E, (B.filter fun x => x ∉ X i).card
        = ∑ x ∈ B, (E.filter fun i => x ∉ X i).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    calc E.card * B.card = ∑ i ∈ E, B.card := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ E, ((L - 1) + (B.filter fun x => x ∉ X i).card) := Finset.sum_le_sum h₁
      _ = E.card * (L - 1) + ∑ x ∈ B, (E.filter fun i => x ∉ X i).card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hswap]
      _ ≤ E.card * (L - 1) + ∑ x ∈ B, e := by gcongr with x hx; exact h₂ x hx
      _ = E.card * (L - 1) + B.card * e := by rw [Finset.sum_const, smul_eq_mul]
  -- `|B| ≤ |E| (L - 1)` and `|E| (|B| - (L - 1)) ≤ |B| e` force `|B| ≤ (e + 1)(L - 1)`
  have h₃ : E.card * (B.card - (L - 1)) ≤ B.card * e := by
    have : E.card * B.card = E.card * (L - 1) + E.card * (B.card - (L - 1)) := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' hbk.le]
    omega
  have h₄ : B.card * (B.card - (L - 1)) ≤ B.card * ((L - 1) * e) := by
    calc B.card * (B.card - (L - 1)) ≤ E.card * (L - 1) * (B.card - (L - 1)) :=
          Nat.mul_le_mul_right _ hα
      _ = (L - 1) * (E.card * (B.card - (L - 1))) := by ring
      _ ≤ (L - 1) * (B.card * e) := Nat.mul_le_mul_left _ h₃
      _ = B.card * ((L - 1) * e) := by ring
  have h₅ : B.card - (L - 1) ≤ (L - 1) * e := Nat.le_of_mul_le_mul_left h₄ (by omega)
  have h₆ : (e + 1) * (L - 1) = e * (L - 1) + (L - 1) := by ring
  have h₇ : (L - 1) * e = e * (L - 1) := by ring
  omega

/-- **Lemma 6.2 [BCGM25]** (with the corrected bound; see the module docstring). Every MDS
generator whose code has full dimension `ℓ ≥ 2` has mutual correlated agreement for every module
code `MC` in the unique-decoding regime, with error `mdsMCAError_uniqueDecoding MC ℓ |S|`:
`(⌊n·γ⌋ + 1)·(ℓ - 1) / |S|` below `δ_C / (ℓ + 1)`, and the trivial bound `1` beyond.

The bound is the seed count `card_filter_isMCA_le_of_isMDSGenerator`, converted to a probability
by `mcaError_le_of_exists_exceptional_set` with the set of bad seeds as the exceptional set. -/
lemma isMCAGenerator_of_isMDSGenerator_uniqueDecoding {S : Type} [Nonempty S] [Fintype S]
    [DecidableEq F]
    [DecidableEq A] [Nonempty ι]
    (G : Generator S ℓ F)
    (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (hℓ : 2 ≤ Fintype.card ℓ)
    (MC : ModuleCode ι F A) :
  IsMCAGenerator G (mdsMCAError_uniqueDecoding MC (Fintype.card ℓ) (Fintype.card S)) MC := by
  classical
  intro γ
  simp only [mdsMCAError_uniqueDecoding]
  split_ifs with hγ
  · have hbound := mcaError_le_of_exists_exceptional_set G MC γ
      (((⌊(γ : ℝ) * Fintype.card ι⌋₊ + 1) * (Fintype.card ℓ - 1) : ℕ) : ℝ) fun U =>
        ⟨Finset.univ.filter fun x => IsMCA G MC x U γ,
          by exact_mod_cast card_filter_isMCA_le_of_isMDSGenerator G hG hdim hℓ MC U γ.2.1 hγ,
          fun x hx h => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
    refine hbound.trans (le_of_eq ?_)
    unfold ENNReal.ofReal
    congr 2
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pred (by omega), mul_div_assoc,
      mul_comm (γ : ℝ)]
  · simpa using mcaError_le_one G MC γ

/-- Every MDS generator whose code has full dimension `ℓ ≥ 2` has MCA for every module code
`MC`, with error `mdsMCAError MC ℓ |S| η`, for every slack `0 < η < 1`. The generator-matrix
hypotheses constrain `G` over the base field only; the tested code's alphabet is any `F`-module.

Sorried: the unique-decoding regime is `isMCAGenerator_of_isMDSGenerator_uniqueDecoding` (via
`mdsMCAError_eq_uniqueDecoding`); the list-decoding regime is not formalized yet. -/
theorem isMCAGenerator_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq A] [Nonempty ι]
    (G : Generator S ℓ F)
    (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (η : ℝ) (hη : 0 < η ∧ η < 1) (hℓ : 2 ≤ Fintype.card ℓ)
    (MC : ModuleCode ι F A) :
  IsMCAGenerator G (mdsMCAError MC (Fintype.card ℓ) (Fintype.card S) η) MC := by sorry

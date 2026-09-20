/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.MCAGenerator
public import ArkLib.Data.CodingTheory.ProximityGenerator.ExceptionalSet
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Mutual correlated agreement for MDS generators

Every MDS generator whose code has full dimension `ℓ ≥ 2` has mutual correlated agreement for
every module code, with error `mdsMCAError`. The unique-decoding regime is proved
(`mcaError_le_mdsMCAError_of_lt`); the list-decoding regime is open.

## Main statements

* `mdsMCAError` — the MCA error function of an MDS generator, with `mdsMCAError_congr` showing it
  depends on the code only through its block length and relative distance.
* `card_filter_isMCA_le_of_isMDSGenerator` — the seed count behind the unique-decoding regime: at
  most `(⌊n·γ⌋ + 1)·(ℓ - 1)` seeds witness the MCA event for a fixed word family.
* `mcaError_le_mdsMCAError_of_lt` — MCA for MDS generators in the unique-decoding regime
  (Lemma 6.2 [BCGM25], with the corrected bound below): the `mdsMCAError` bound at every radius
  below `δ_C / (ℓ + 1)`.
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
  classical
  have hδ := congrArg (Rat.cast (K := ℝ))
    (Code.minDist_div_card_eq_minRelHammingDistCode MC.carrier)
  push_cast at hδ
  set n := Fintype.card ι with hn
  set L := Fintype.card ℓ with hL
  set r := L - 1 with hr
  set e := ⌊γ * n⌋₊ with he
  set B := Finset.univ.filter fun x => IsMCA G MC x U γ with hB
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  have he_le : (e : ℝ) ≤ γ * n := Nat.floor_le (by positivity)
  rw [← hδ, div_div, lt_div_iff₀ (by positivity)] at hγ
  have hd : e + L * e < Code.minDist MC.carrier := by
    exact_mod_cast (by nlinarith : (e : ℝ) + L * e < Code.minDist MC.carrier)
  by_contra hlt
  push Not at hlt
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
  set xs : ℓ → S := fun k => (f k).1 with hxs
  have hxsB : ∀ k, xs k ∈ B := fun k => (f k).2
  set M : Matrix ℓ ℓ F := Matrix.of fun k j => G (xs k) j with hM
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp
    (isUnit_of_isMDSGenerator G hG hdim (Subtype.val_injective.comp f.injective)))
  set cs : ℓ → ι → A := fun j => ∑ k, M⁻¹ j k • c (xs k) with hcs
  have hcs_mem : ∀ j, cs j ∈ MC := fun j =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hc _ (hxsB k))
  have hcs_apply : ∀ j i, cs j i = ∑ k, M⁻¹ j k • c (xs k) i := fun j i => by
    simp [hcs, Finset.sum_apply]
  have hU_eq : ∀ j i, U j i = ∑ k, M⁻¹ j k • ∑ j', G (xs k) j' • U j' i := fun j i =>
    (sum_smul_sum_smul_eq_of_mul_eq_one hNM (fun j => U j i) j).symm
  set Tc : Finset ι := Finset.univ.biUnion fun k => (T (xs k))ᶜ with hTc_def
  have hTc_card : Tc.card ≤ L * e :=
    (Finset.card_biUnion_le_card_mul _ _ _ fun k _ => hTc _ (hxsB k)).trans_eq
      (by rw [Finset.card_univ])
  have hTc_mem : ∀ i, i ∉ Tc → ∀ k, i ∈ T (xs k) := fun i hi k => by_contra fun h =>
    hi (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_compl.mpr h⟩)
  have hU_cs : ∀ i, i ∉ Tc → ∀ j, U j i = cs j i := fun i hi j => by
    rw [hU_eq, hcs_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hcT _ (hxsB k) i (hTc_mem i hi k)]
  set w : S → ι → A := fun x => ∑ j, G x j • cs j with hw
  have hw_mem : ∀ x, w x ∈ MC := fun x =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcs_mem j)
  have hw_apply : ∀ x i, w x i = ∑ j, G x j • cs j i := fun x i => by
    simp [hw, Finset.sum_apply]
  have hcw_off : ∀ x ∈ B, ∀ i ∈ T x, i ∉ Tc → c x i = w x i := fun x hx i hiT hiTc => by
    rw [← hcT x hx i hiT, hw_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [hU_cs i hiTc j]
  have hcw : ∀ x ∈ B, c x = w x := fun x hx =>
    Code.eq_of_disagreementCols_subset_of_card_lt_minDist (hc x hx) (hw_mem x) ((T x)ᶜ ∪ Tc)
      (fun i hi => by
        by_contra h
        rw [Finset.mem_union, not_or, Finset.mem_compl, not_not] at h
        exact Code.mem_disagreementCols.mp hi (hcw_off x hx i h.1 h.2))
      (lt_of_le_of_lt ((Finset.card_union_le _ _).trans (Nat.add_le_add (hTc x hx) hTc_card)) hd)
  have hagree : ∀ x ∈ B, ∀ i ∈ T x, ∑ j, G x j • U j i = ∑ j, G x j • cs j i :=
    fun x hx i hi => by rw [hcT x hx i hi, hcw x hx, hw_apply]
  set E := Finset.univ.filter fun i => ∃ j, U j i ≠ cs j i with hE
  set X : ι → Finset S :=
    fun i => Finset.univ.filter fun x => ∑ j, G x j • U j i = ∑ j, G x j • cs j i with hX
  have hE_mem : ∀ i, i ∉ E → ∀ j, U j i = cs j i := fun i hi j => by_contra fun h =>
    hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, h⟩)
  have hX_card : ∀ i ∈ E, (X i).card ≤ r := fun i hi =>
    card_filter_sum_smul_eq_le_of_isMDSGenerator G hG hdim (v := fun j => U j i)
      (w := fun j => cs j i) (Function.ne_iff.mpr (Finset.mem_filter.mp hi).2)
  have hE_of_bad : ∀ x ∈ B, ∃ i ∈ T x, i ∈ E := fun x hx => by
    by_contra hnone
    push Not at hnone
    obtain ⟨j, hj⟩ := hTbad x hx
    exact hj ((mem_projectedCodeSubmod_iff MC (T x) _).mpr
      ⟨cs j, hcs_mem j, funext fun i => hE_mem i.1 (hnone i.1 i.2) j⟩)
  have hα : B.card ≤ E.card * r :=
    (Finset.card_le_card fun x hx => by
      obtain ⟨i, hiT, hiE⟩ := hE_of_bad x hx
      exact Finset.mem_biUnion.mpr
        ⟨i, hiE, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree x hx i hiT⟩⟩).trans
      (Finset.card_biUnion_le_card_mul E X r hX_card)
  have hm : ∀ i ∈ E, B.card - r ≤ (B.bipartiteAbove (fun i x => x ∉ X i) i).card := fun i hi =>
    (Nat.sub_le_sub_left (hX_card i hi) _).trans ((Finset.le_card_sdiff _ _).trans_eq
      (congrArg Finset.card Finset.filter_notMem_eq_sdiff.symm))
  have hn : ∀ x ∈ B, (E.bipartiteBelow (fun i x => x ∉ X i) x).card ≤ e := fun x hx =>
    (Finset.card_le_card fun i hi => Finset.mem_compl.mpr fun hiT =>
      ((Finset.mem_bipartiteBelow fun i x => x ∉ X i).mp hi).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree x hx i hiT⟩)).trans (hTc x hx)
  have hβ : E.card * (B.card - r) ≤ B.card * e := Finset.card_mul_le_card_mul _ hm hn
  have hfin : B.card * (B.card - r) ≤ B.card * (e * r) :=
    calc B.card * (B.card - r) ≤ E.card * r * (B.card - r) := Nat.mul_le_mul_right _ hα
      _ = r * (E.card * (B.card - r)) := by ring
      _ ≤ r * (B.card * e) := Nat.mul_le_mul_left _ hβ
      _ = B.card * (e * r) := by ring
  have hsub : B.card - r ≤ e * r := Nat.le_of_mul_le_mul_left hfin (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hlt
  omega

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
lemma mcaError_le_mdsMCAError_of_lt {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq A] [Nonempty ι] (G : Generator S ℓ F) (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (hℓ : 2 ≤ Fintype.card ℓ) (MC : ModuleCode ι F A) (η : ℝ) (γ : I)
    (hγ : (γ : ℝ) < (Code.minRelHammingDistCode MC.carrier : ℝ) / (Fintype.card ℓ + 1)) :
    mcaError G MC γ ≤ (mdsMCAError MC (Fintype.card ℓ) (Fintype.card S) η γ : ENNReal) := by
  classical
  have hbound := mcaError_le_of_exists_exceptional_set G MC γ
    (((⌊(γ : ℝ) * Fintype.card ι⌋₊ + 1) * (Fintype.card ℓ - 1) : ℕ) : ℝ) fun U =>
      ⟨Finset.univ.filter fun x => IsMCA G MC x U γ,
        by exact_mod_cast card_filter_isMCA_le_of_isMDSGenerator G hG hdim hℓ MC U γ.2.1 hγ,
        fun x hx h => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
  refine hbound.trans (le_of_eq ?_)
  simp only [mdsMCAError, if_pos hγ]
  unfold ENNReal.ofReal
  congr 2
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pred (by omega), mul_div_assoc,
    mul_comm (γ : ℝ)]

/-- Every MDS generator whose code has full dimension `ℓ ≥ 2` has MCA for every module code `MC`,
with error `mdsMCAError MC ℓ |S| η`, for every slack `0 < η < 1`. The generator-matrix hypotheses
constrain `G` over the base field only; the tested code's alphabet is any `F`-module.
Theorem 6.1 [BCGM25]. -/
theorem isMCAGenerator_of_isMDSGenerator {S : Type} [Nonempty S] [Fintype S] [DecidableEq F]
    [DecidableEq A] [Nonempty ι]
    (G : Generator S ℓ F)
    (hG : IsMDSGenerator G)
    (hdim : LinearCode.dim (LinearCode.fromColGenMat (M_G G)) = Fintype.card ℓ)
    (η : ℝ) (hη : 0 < η ∧ η < 1) (hℓ : 2 ≤ Fintype.card ℓ)
    (MC : ModuleCode ι F A) :
  IsMCAGenerator G (mdsMCAError MC (Fintype.card ℓ) (Fintype.card S) η) MC := by
  intro γ
  by_cases hγ : (γ : ℝ) < (Code.minRelHammingDistCode MC.carrier : ℝ) / (Fintype.card ℓ + 1)
  · exact mcaError_le_mdsMCAError_of_lt G hG hdim hℓ MC η γ hγ
  · sorry

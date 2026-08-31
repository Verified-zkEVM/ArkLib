/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.LargeAlphabet.Centers

/-!
# Large-alphabet barrier: the local neighbourhood bound and the pigeonhole barrier

The common-disagreement-intersection lemma, the **local neighbourhood bound** that
turns `Λ(C, ·) ≤ ℓ` into a cap on how many codewords sit near a centre
(`local_neighborhood_bound`), the **deterministic pigeonhole bound**
(`deterministic_pigeonhole_bound`) that replaces the source's probabilistic step, and the parameter
windows the rounded barrier needs — the density thresholds, the constant bounds, and the
upper/lower family densities.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview and the
references, and `Bounds/LargeAlphabet.lean` for the two theorems this development serves.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code

namespace LargeAlphabetBarrier

/-- **Many large sets share a large `ℓ`-wise intersection.** Given `M ≥ ⌈4ℓ²/p⌉` subsets of the
coordinates each of size `> p·n`, some `ℓ` of them meet in at least `⌈(3p^ℓ/4)·n⌉` coordinates.
This is what lets a balanced centre be built from `ℓ` nearby codewords. -/
theorem common_disagreement_intersection :
    ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (M : ℕ), Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
        ∀ S : Fin M → Finset ι,
          (∀ j, Nat.floor (p * Fintype.card ι) < (S j).card) →
          ∃ J : Finset (Fin M), J.card = ℓ ∧
            Nat.ceil ((3 * p ^ ℓ / 4) * Fintype.card ι) ≤
              ({i : ι | ∀ j, j ∈ J → i ∈ S j} : Set ι).ncard := by
  classical
  intro ℓ hℓ p hp hp_lt ι _ _ M hM S hS
  let n := Fintype.card ι
  have hℓR : (0 : ℝ) < ℓ := by
    exact_mod_cast (show 0 < ℓ by omega)
  have hℓOne : (1 : ℝ) ≤ ℓ := by
    exact_mod_cast (show 1 ≤ ℓ by omega)
  have hℓBound : (ℓ : ℝ) ≤ 4 * (ℓ : ℝ) ^ 2 / p := by
    rw [le_div_iff₀ hp]
    calc
      (ℓ : ℝ) * p ≤ (ℓ : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hp_lt.le hℓR.le
      _ = (ℓ : ℝ) := by ring
      _ = (ℓ : ℝ) * 1 := by ring
      _ ≤ (ℓ : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_left hℓOne hℓR.le
      _ = (ℓ : ℝ) ^ 2 := by ring
      _ ≤ 4 * (ℓ : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (ℓ : ℝ)]
  have hℓCeil : ℓ ≤ Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) := by
    exact_mod_cast hℓBound.trans (Nat.le_ceil (4 * (ℓ : ℝ) ^ 2 / p))
  have hℓM : ℓ ≤ M := hℓCeil.trans hM
  have hMpos : 0 < M := lt_of_lt_of_le (by omega : 0 < ℓ) hℓM
  let j0 : Fin M := ⟨0, hMpos⟩
  have hn : 0 < n := by
    have hcardPos : 0 < (S j0).card := Nat.zero_lt_of_lt (hS j0)
    have hle : (S j0).card ≤ Fintype.card ι := Finset.card_le_univ _
    simpa only [n] using hcardPos.trans_le hle
  let incidence : ι → ℕ := fun i =>
    (Finset.univ.filter fun j => i ∈ S j).card
  have hpoint : ∀ j : Fin M, p * n < ((S j).card : ℝ) := by
    intro j
    exact Nat.lt_of_floor_lt (hS j)
  have hsumSets : p * M * n ≤ ∑ j, ((S j).card : ℝ) := by
    have hconst : (∑ _j : Fin M, p * n) = p * M * n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
    rw [← hconst]
    exact Finset.sum_le_sum fun j hj => (hpoint j).le
  have hincReal :
      (∑ i, (incidence i : ℝ)) = ∑ j, ((S j).card : ℝ) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (incidence_sum_double_count S)
    simpa only [incidence, Nat.cast_sum] using h
  have hsumInc : p * M * n ≤ ∑ i, (incidence i : ℝ) := by
    calc
      p * M * n ≤ ∑ j, ((S j).card : ℝ) := hsumSets
      _ = ∑ i, (incidence i : ℝ) := hincReal.symm
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let a : Fin n → ℕ := fun k => incidence (e.symm k)
  have hreindexReal :
      (∑ i, (incidence i : ℝ)) = ∑ k, (a k : ℝ) := by
    simpa only [a, Equiv.symm_apply_apply] using
      (e.sum_comp fun k => (a k : ℝ))
  have hsumA : p * M * n ≤ ∑ k, (a k : ℝ) :=
    hsumInc.trans_eq hreindexReal
  have hmomentA :=
    incidence_moment_lower ℓ M n p hℓ hn hp hp_lt hM a hsumA
  have hreindexChoose :
      (∑ i, (Nat.choose (incidence i) ℓ : ℝ)) =
        ∑ k, (Nat.choose (a k) ℓ : ℝ) := by
    simpa only [a, Equiv.symm_apply_apply] using
      (e.sum_comp fun k => (Nat.choose (a k) ℓ : ℝ))
  have hmomentInc :
      (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
        ∑ i, (Nat.choose (incidence i) ℓ : ℝ) := by
    calc
      (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
          ∑ k, (Nat.choose (a k) ℓ : ℝ) := hmomentA
      _ = ∑ i, (Nat.choose (incidence i) ℓ : ℝ) := hreindexChoose.symm
  let common : Finset (Fin M) → Finset ι := fun J =>
    Finset.univ.filter fun i => ∀ j ∈ J, i ∈ S j
  have hdoubleReal :
      (∑ i, (Nat.choose (incidence i) ℓ : ℝ)) =
        ∑ J ∈ Finset.univ.powersetCard ℓ, ((common J).card : ℝ) := by
    have h := congrArg (fun z : ℕ => (z : ℝ))
      (incidence_double_count ℓ S)
    norm_num only [Nat.cast_sum] at h
    dsimp only [incidence, common]
    convert h using 1
    congr!
  have hmomentCommon :
      (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
        ∑ J ∈ Finset.univ.powersetCard ℓ, ((common J).card : ℝ) :=
    hmomentInc.trans_eq hdoubleReal
  let P : Finset (Finset (Fin M)) := Finset.univ.powersetCard ℓ
  have hPnonempty : P.Nonempty := by
    apply Finset.powersetCard_nonempty_of_le
    simpa only [P, Finset.card_univ, Fintype.card_fin] using hℓM
  let x : ℝ := (3 * p ^ ℓ / 4) * n
  by_cases hex : ∃ J ∈ P, Nat.ceil x ≤ (common J).card
  · obtain ⟨J, hJP, hJbound⟩ := hex
    have hJcard : J.card = ℓ :=
      (Finset.mem_powersetCard.mp hJP).2
    have hcoe : (common J : Set ι) =
        {i : ι | ∀ j, j ∈ J → i ∈ S j} := by
      ext i
      simp only [common, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq]
    have hncard :
        ({i : ι | ∀ j, j ∈ J → i ∈ S j} : Set ι).ncard =
          (common J).card := by
      rw [← Set.ncard_coe_finset, hcoe]
    refine ⟨J, hJcard, ?_⟩
    rw [hncard]
    simpa only [x, n] using hJbound
  · have hltNat : ∀ J ∈ P, (common J).card < Nat.ceil x := by
      intro J hJP
      exact Nat.lt_of_not_ge fun hge => hex ⟨J, hJP, hge⟩
    have hltReal : ∀ J ∈ P, ((common J).card : ℝ) < x := by
      intro J hJP
      rw [← Nat.add_one_le_ceil_iff]
      exact Nat.succ_le_iff.mpr (hltNat J hJP)
    have hsumLt :
        (∑ J ∈ P, ((common J).card : ℝ)) < ∑ J ∈ P, x :=
      Finset.sum_lt_sum_of_nonempty hPnonempty hltReal
    have hconst :
        (∑ J ∈ P, x) = (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n := by
      simp only [P, x, Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hupper :
        (∑ J ∈ Finset.univ.powersetCard ℓ, ((common J).card : ℝ)) <
          (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n := by
      simpa only [P, hconst] using hsumLt
    exfalso
    exact (not_lt_of_ge hmomentCommon) hupper

theorem balanced_center_from_far_family
    (ℓ M : ℕ) (hℓ : 2 ≤ ℓ) (p : ℝ) (hp : 0 < p) (hp_lt : p < 1)
    (hM : Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M)
    {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (c : ι → A) (v : Fin M → ι → A)
    (hfar : ∀ j, Nat.floor (p * Fintype.card ι) < hammingDist c (v j))
    (hnear : ∀ j, hammingDist c (v j) ≤
      Nat.floor (boostedRadius ℓ p * Fintype.card ι))
    (hsize : 8 * (ℓ : ℝ) ≤ p ^ ℓ * Fintype.card ι) :
    ∃ sel : Fin ℓ → Fin M, Function.Injective sel ∧
      ∃ y : ι → A,
        hammingDist c y ≤ Nat.floor (p * Fintype.card ι) ∧
        ∀ k, hammingDist (v (sel k)) y ≤
          Nat.floor (p * Fintype.card ι) := by
  classical
  let S : Fin M → Finset ι := fun j =>
    Finset.univ.filter fun i => c i ≠ v j i
  have hScard : ∀ j, Nat.floor (p * Fintype.card ι) < (S j).card := by
    intro j
    simpa only [S, hammingDist] using hfar j
  obtain ⟨J, hJcard, hcommon⟩ :=
    common_disagreement_intersection ℓ hℓ p hp hp_lt M hM S hScard
  let e : Fin ℓ ≃ J := (Finset.equivFinOfCardEq hJcard).symm
  let sel : Fin ℓ → Fin M := fun k => (e k).1
  have hselinj : Function.Injective sel := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  let u : Fin ℓ → ι → A := fun k => v (sel k)
  have hcommonSet :
      ({i : ι | ∀ j, j ∈ J → i ∈ S j} : Set ι) =
        {i : ι | ∀ k, c i ≠ u k i} := by
    ext i
    constructor
    · intro hi k
      have hik := hi (sel k) (e k).2
      exact (Finset.mem_filter.mp hik).2
    · intro hi j hj
      let q : J := ⟨j, hj⟩
      obtain ⟨k, hk⟩ := e.surjective q
      have hsel : sel k = j := by
        exact congrArg Subtype.val hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hik := hi k
      simpa only [u, hsel] using hik
  have hcommonU :
      Nat.ceil ((3 * p ^ ℓ / 4) * Fintype.card ι) ≤
        ({i : ι | ∀ k, c i ≠ u k i} : Set ι).ncard := by
    rw [← hcommonSet]
    exact hcommon
  obtain ⟨y, hyc, hyu⟩ :=
    balanced_center_construction ℓ hℓ p hp hp_lt c u
      (by
        intro k
        simpa only [u] using hnear (sel k))
      hsize hcommonU
  refine ⟨sel, hselinj, y, hyc, ?_⟩
  intro k
  simpa only [u] using hyu k

open _root_.Code in
/-- **The local neighbourhood bound.** A list size of at most `ℓ` at radius `p` caps how many
codewords sit within the *boosted* radius of any one codeword, at `ℓ + ⌈4ℓ²/p⌉`. Proved by feeding
the balanced-centre construction a hypothetical excess. -/
theorem local_neighborhood_bound :
    ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
        {A : Type} [Fintype A] [DecidableEq A]
        (C : Set (ι → A)), Lambda C p ≤ (ℓ : ℕ∞) →
        8 * (ℓ : ℝ) ≤ p ^ ℓ * Fintype.card ι →
        ∀ c ∈ C,
          ({x : ι → A | x ∈ C ∧
            hammingDist c x ≤
              Nat.floor (boostedRadius ℓ p * Fintype.card ι)} : Set (ι → A)).ncard
            ≤ ℓ + Nat.ceil (4 * ((ℓ : ℝ) ^ 2) / p) := by
  classical
  intro ℓ hℓ p hp hp_lt ι _ _ _ A _ _ C hLambda hsize c hc
  let n := Fintype.card ι
  let r := Nat.floor (p * n)
  let r' := Nat.floor (boostedRadius ℓ p * n)
  let M := Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p)
  let I : Set (ι → A) :=
    {x : ι → A | x ∈ C ∧ hammingDist c x ≤ r}
  let B : Set (ι → A) :=
    {x : ι → A | x ∈ C ∧ hammingDist c x ≤ r'}
  have hpoint := (Code.Lambda_le_iff_forall_ncard_le.mp hLambda) c
  have hcloseI : closeCodewordsRel C c p = I := by
    simpa only [I, r, n, hammingDist_comm] using
      closeCodewordsRel_eq_setOf C p hp.le c
  rw [hcloseI] at hpoint
  have hIcard : I.ncard ≤ ℓ := hpoint.2
  have harith := balanced_center_arithmetic ℓ p n hℓ hp hp_lt (by
    simpa only [n] using hsize)
  have hrle : r ≤ r' := by
    simpa only [r, r'] using harith.1
  have hIB : I ⊆ B := by
    intro x hx
    change x ∈ C ∧ hammingDist c x ≤ r at hx
    change x ∈ C ∧ hammingDist c x ≤ r'
    exact ⟨hx.1, hx.2.trans hrle⟩
  change B.ncard ≤ ℓ + M
  by_contra hnot
  have hBlarge : ℓ + M < B.ncard := Nat.lt_of_not_ge hnot
  obtain ⟨v, hvinj, hvBI⟩ :=
    injective_family_of_ncard_diff I B ℓ M hIB hIcard hBlarge
  have hvC : ∀ j, v j ∈ C := by
    intro j
    have hvB := (hvBI j).1
    change v j ∈ C ∧ hammingDist c (v j) ≤ r' at hvB
    exact hvB.1
  have hvnear : ∀ j, hammingDist c (v j) ≤
      Nat.floor (boostedRadius ℓ p * Fintype.card ι) := by
    intro j
    have hvB := (hvBI j).1
    change v j ∈ C ∧ hammingDist c (v j) ≤ r' at hvB
    simpa only [r', n] using hvB.2
  have hvfar : ∀ j, Nat.floor (p * Fintype.card ι) <
      hammingDist c (v j) := by
    intro j
    have hvnotI := (hvBI j).2
    have hnotle : ¬hammingDist c (v j) ≤ r := by
      intro hle
      apply hvnotI
      change v j ∈ C ∧ hammingDist c (v j) ≤ r
      exact ⟨hvC j, hle⟩
    simpa only [r, n] using Nat.lt_of_not_ge hnotle
  obtain ⟨sel, hselinj, y, hyc, hyu⟩ :=
    balanced_center_from_far_family ℓ M hℓ p hp hp_lt
      (by exact le_rfl) c v hvfar hvnear hsize
  let u : Fin ℓ → ι → A := fun k => v (sel k)
  have huinj : Function.Injective u := hvinj.comp hselinj
  have huC : ∀ k, u k ∈ C := by
    intro k
    exact hvC (sel k)
  have huc : ∀ k, u k ≠ c := by
    intro k hEq
    have hpos := hvfar (sel k)
    change Nat.floor (p * Fintype.card ι) < hammingDist c (u k) at hpos
    rw [hEq, hammingDist_self] at hpos
    omega
  exact lambda_contradiction_of_injective_center ℓ C p hp.le c hc u
    huinj huC huc y hyc (by
      intro k
      simpa only [u] using hyu k) hLambda

theorem singleton_fiber_card_le_image
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (s.filter fun x => ∀ y ∈ s, f y = f x → y = x).card ≤
      (s.image f).card := by
  let good : Finset α :=
    s.filter fun x => ∀ y ∈ s, f y = f x → y = x
  have hinj : Set.InjOn f (good : Set α) := by
    intro x hx y hy hxy
    have hxgood := (Finset.mem_filter.mp hx).2
    have hys := (Finset.mem_filter.mp hy).1
    exact (hxgood y hys hxy.symm).symm
  have himage : (good.image f).card = good.card :=
    Finset.card_image_of_injOn hinj
  have hsub : good.image f ⊆ s.image f := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hxgood, rfl⟩
    exact Finset.mem_image.mpr
      ⟨x, (Finset.mem_filter.mp hxgood).1, rfl⟩
  change good.card ≤ (s.image f).card
  rw [← himage]
  exact Finset.card_le_card hsub

theorem many_nonsingleton_fibers
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (f : X → Y) (B : ℕ)
    (himage : (s.image f).card ≤ B) (hlarge : 2 * B ≤ s.card) :
    s.card ≤ 2 *
      (s.filter fun x => ∃ y ∈ s, y ≠ x ∧ f y = f x).card := by
  classical
  let single : Finset X :=
    s.filter fun x => ∀ y ∈ s, f y = f x → y = x
  let multi : Finset X :=
    s.filter fun x => ∃ y ∈ s, y ≠ x ∧ f y = f x
  have hsingle : single.card ≤ B := by
    exact (singleton_fiber_card_le_image s f).trans himage
  have hcomp : single = s \ multi := by
    ext x
    simp only [single, multi, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hxs, huniq⟩
      refine ⟨hxs, ?_⟩
      rintro ⟨_, y, hys, hyne, heq⟩
      exact hyne (huniq y hys heq)
    · rintro ⟨hxs, hnot⟩
      refine ⟨hxs, ?_⟩
      intro y hys heq
      by_contra hyne
      apply hnot
      exact ⟨hxs, y, hys, hyne, heq⟩
  have hpart : single.card + multi.card = s.card := by
    rw [hcomp]
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  change s.card ≤ 2 * multi.card
  omega

theorem many_restriction_alternatives
    {ι A : Type} [Fintype ι] [DecidableEq ι]
      [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (hC : C.Finite) (S : Finset ι)
    (aFamily : ℕ) (hScard : S.card = aFamily)
    (hmany : 2 * Fintype.card A ^ aFamily ≤ C.ncard) :
    C.ncard ≤ 2 *
      (hC.toFinset.filter fun c =>
        ∃ z ∈ hC.toFinset, z ≠ c ∧ ∀ i ∈ S, z i = c i).card := by
  classical
  let code : Finset (ι → A) := hC.toFinset
  let restrict : (ι → A) → (S → A) := fun c i => c i.1
  have hcodecard : code.card = C.ncard := by
    rw [← Set.ncard_coe_finset, hC.coe_toFinset]
  have himage : (code.image restrict).card ≤
      Fintype.card A ^ aFamily := by
    calc
      (code.image restrict).card ≤ Fintype.card (S → A) :=
        Finset.card_le_univ _
      _ = Fintype.card A ^ aFamily := by
        rw [Fintype.card_fun, Fintype.card_coe, hScard]
  have hlarge : 2 * Fintype.card A ^ aFamily ≤ code.card := by
    rw [hcodecard]
    exact hmany
  have hmulti := many_nonsingleton_fibers code restrict
    (Fintype.card A ^ aFamily) himage hlarge
  have hfilter :
      code.filter (fun c =>
        ∃ z ∈ code, z ≠ c ∧ restrict z = restrict c) =
      code.filter (fun c =>
        ∃ z ∈ code, z ≠ c ∧ ∀ i ∈ S, z i = c i) := by
    ext c
    simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨z, hz, hne, heq⟩
      refine ⟨z, hz, hne, ?_⟩
      intro i hi
      exact congrFun heq ⟨i, hi⟩
    · rintro ⟨z, hz, hne, hagree⟩
      refine ⟨z, hz, hne, ?_⟩
      funext i
      exact hagree i.1 i.2
  rw [hfilter] at hmulti
  simpa only [code, hcodecard] using hmulti

theorem good_base_word
    (W aFamily aUnion : ℕ)
    {ι A : Type} [Fintype ι] [DecidableEq ι]
      [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (hC : C.Finite) (hA : 2 ≤ Fintype.card A)
    (family : LargeUnionFamily ι W aFamily aUnion)
    (hmany : 2 * Fintype.card A ^ aFamily ≤ C.ncard) :
    ∃ c₀ : ι → A, c₀ ∈ C ∧
      ∃ good : Finset (Finset ι), good ⊆ family.sets ∧
        family.sets.card ≤ 2 * good.card ∧
        ∃ alt : Finset ι → ι → A,
          ∀ S ∈ good, alt S ∈ C ∧ alt S ≠ c₀ ∧
            ∀ i ∈ S, alt S i = c₀ i := by
  classical
  let code : Finset (ι → A) := hC.toFinset
  let P : (ι → A) → Finset ι → Prop := fun c S =>
    ∃ z ∈ code, z ≠ c ∧ ∀ i ∈ S, z i = c i
  have hcodecard : code.card = C.ncard := by
    rw [← Set.ncard_coe_finset, hC.coe_toFinset]
  have hqpos : 0 < Fintype.card A := by omega
  have hleftpos : 0 < 2 * Fintype.card A ^ aFamily :=
    Nat.mul_pos (by omega) (pow_pos hqpos aFamily)
  have hcodepos : 0 < code.card := by
    rw [hcodecard]
    exact hleftpos.trans_le hmany
  have hcode : code.Nonempty := Finset.card_pos.mp hcodepos
  have hcol : ∀ S ∈ family.sets,
      code.card ≤ 2 * (code.filter fun c => P c S).card := by
    intro S hS
    have h := many_restriction_alternatives C hC S aFamily
      (family.card_each S hS) hmany
    simpa only [code, P, hcodecard] using h
  obtain ⟨c₀, hc₀code, hc₀good⟩ :=
    good_base_by_double_count code family.sets P hcode hcol
  let good : Finset (Finset ι) := family.sets.filter fun S => P c₀ S
  have hgoodsub : good ⊆ family.sets := Finset.filter_subset _ _
  have hgoodcard : family.sets.card ≤ 2 * good.card := by
    simpa only [good] using hc₀good
  have haltExists : ∀ S ∈ good,
      ∃ z ∈ code, z ≠ c₀ ∧ ∀ i ∈ S, z i = c₀ i := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  have hAnonempty : Nonempty A := Fintype.card_pos_iff.mp hqpos
  let defaultWord : ι → A := fun _ => Classical.choice hAnonempty
  let alt : Finset ι → ι → A := fun S =>
    if hS : S ∈ good then Classical.choose (haltExists S hS) else defaultWord
  have haltSpec : ∀ S ∈ good,
      alt S ∈ code ∧ alt S ≠ c₀ ∧ ∀ i ∈ S, alt S i = c₀ i := by
    intro S hS
    dsimp only [alt]
    rw [dif_pos hS]
    exact Classical.choose_spec (haltExists S hS)
  refine ⟨c₀, ?_, good, hgoodsub, hgoodcard, alt, ?_⟩
  · rw [← hC.coe_toFinset]
    exact hc₀code
  · intro S hS
    have hs := haltSpec S hS
    refine ⟨?_, hs.2.1, hs.2.2⟩
    rw [← hC.coe_toFinset]
    exact hs.1

open _root_.Code in
theorem deterministic_pigeonhole_bound :
    DeterministicPigeonholeBound := by
  classical
  unfold DeterministicPigeonholeBound
  intro ℓ n radius boosted hℓ hn ι A _ _ _ _ C hA hcard hC
    params hW blocks family hfamilyDisjoint hsep hmany hLambda
  obtain ⟨c₀, hc₀, good, hgoodSub, hgoodCard, alt, halt⟩ :=
    good_base_word params.W params.aFamily params.aUnion
      C hC hA family hmany
  let goodFamily : LargeUnionFamily ι params.W
      params.aFamily params.aUnion :=
    { sets := good
      card_each := by
        intro S hS
        exact family.card_each S (hgoodSub hS)
      large_union := by
        intro T hT hTcard
        exact family.large_union T (hT.trans hgoodSub) hTcard }
  have haltC : ∀ S ∈ goodFamily.sets, alt S ∈ C := by
    intro S hS
    exact (halt S hS).1
  have haltNe : ∀ S ∈ goodFamily.sets, alt S ≠ c₀ := by
    intro S hS
    exact (halt S hS).2.1
  have haltAgree : ∀ S ∈ goodFamily.sets,
      ∀ i ∈ S, alt S i = c₀ i := by
    intro S hS
    exact (halt S hS).2.2
  have hAltFiber := alternative_fiber_bound
    params.W params.aFamily params.aUnion n boosted C hcard
    goodFamily c₀ hc₀ alt haltC haltNe haltAgree hsep
    params.repeated_codeword_contradiction hW
  by_contra hnot
  have hstrict :
      2 * params.W * ℓ * Fintype.card A ^ params.dZero <
        family.sets.card := Nat.lt_of_not_ge hnot
  let K : ℕ := params.W * ℓ * Fintype.card A ^ params.dZero
  have hstrictK : 2 * K < family.sets.card := by
    simpa only [K, Nat.mul_assoc] using hstrict
  have htwice : 2 * K < 2 * good.card :=
    hstrictK.trans_le hgoodCard
  have hKgood : K < good.card := by omega
  have hqpos : 0 < Fintype.card A := by omega
  have hprodPos :
      0 < Fintype.card A ^ params.dZero * (params.W * ℓ) := by
    exact Nat.mul_pos (pow_pos hqpos params.dZero)
      (Nat.mul_pos hW (by omega))
  have hlargeFiber :
      Fintype.card A ^ params.dZero * (params.W * ℓ) ≤ good.card := by
    have heq : Fintype.card A ^ params.dZero * (params.W * ℓ) = K := by
      dsimp only [K]
      ring
    rw [heq]
    omega
  have hgoodNonempty : good.Nonempty := by
    apply Finset.card_pos.mp
    exact hprodPos.trans_le hlargeFiber
  let restrictZero : Finset ι → (blocks.zero → A) := fun S i => alt S i.1
  have hrestrictImage : (good.image restrictZero).card ≤
      Fintype.card A ^ params.dZero := by
    calc
      (good.image restrictZero).card ≤ Fintype.card (blocks.zero → A) :=
        Finset.card_le_univ _
      _ = Fintype.card A ^ params.dZero := by
        rw [Fintype.card_fun, Fintype.card_coe, blocks.card_zero]
  obtain ⟨common, hcommonImage, hsameCard⟩ :=
    large_fiber_of_image_bound good restrictZero
      (Fintype.card A ^ params.dZero) (params.W * ℓ)
      hgoodNonempty hrestrictImage hlargeFiber
  let same : Finset (Finset ι) :=
    good.filter fun S => restrictZero S = common
  have hsameSub : same ⊆ good := Finset.filter_subset _ _
  have hsameCard' : params.W * ℓ ≤ same.card := by
    simpa only [same] using hsameCard
  have hsameFiber : ∀ z,
      (same.filter fun S => alt S = z).card < params.W := by
    intro z
    have hsub :
        same.filter (fun S => alt S = z) ⊆
          good.filter (fun S => alt S = z) := by
      intro S hS
      have hs := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨hsameSub hs.1, hs.2⟩
    exact (Finset.card_le_card hsub).trans_lt (hAltFiber z)
  have hdistinct : ℓ ≤ (same.image alt).card :=
    distinct_alternatives_of_bounded_fibers same alt params.W ℓ
      hW hsameCard' hsameFiber
  obtain ⟨chosen, hchosenSame, huinj⟩ :=
    choose_distinct_images same alt ℓ hdistinct
  let u : Fin ℓ → ι → A := fun j => alt (chosen j)
  have hchosenGood : ∀ j, chosen j ∈ good := by
    intro j
    exact hsameSub (hchosenSame j)
  have hchosenFamily : ∀ j, chosen j ∈ family.sets := by
    intro j
    exact hgoodSub (hchosenGood j)
  have hchosenCard : ∀ j, (chosen j).card = params.aFamily := by
    intro j
    exact family.card_each (chosen j) (hchosenFamily j)
  have hchosenDisjoint : ∀ j,
      Disjoint (chosen j) blocks.zero ∧
        ∀ k, Disjoint (chosen j) (blocks.other k) := by
    intro j
    exact hfamilyDisjoint (chosen j) (hchosenFamily j)
  have huAgree : ∀ j, ∀ i ∈ chosen j, u j i = c₀ i := by
    intro j
    exact (halt (chosen j) (hchosenGood j)).2.2
  have huZero : ∀ j, ∀ i, ∀ hi : i ∈ blocks.zero,
      u j i = common ⟨i, hi⟩ := by
    intro j i hi
    have hsame := (Finset.mem_filter.mp (hchosenSame j)).2
    exact congrFun hsame ⟨i, hi⟩
  obtain ⟨y, hyc, hyu⟩ := barrier_center_from_blocks
    ℓ n params.dZero params.dOne params.aFamily hcard blocks
    c₀ chosen u common hchosenCard hchosenDisjoint huAgree huZero
  have hycRadius : hammingDist c₀ y ≤ radius :=
    hyc.trans params.center_block_bound
  have hyuRadius : ∀ j, hammingDist (u j) y ≤ radius := by
    intro j
    exact (hyu j).trans params.other_codeword_bound
  have hιpos : 0 < Fintype.card ι := by
    rw [hcard]
    exact hn
  let : Nonempty ι := Fintype.card_pos_iff.mp hιpos
  have hp : 0 ≤ (radius : ℝ) / n := by positivity
  have hfloor :
      Nat.floor (((radius : ℝ) / n) * Fintype.card ι) = radius := by
    rw [hcard]
    exact floor_div_mul_self radius n hn
  have huC : ∀ j, u j ∈ C := by
    intro j
    exact (halt (chosen j) (hchosenGood j)).1
  have huc : ∀ j, u j ≠ c₀ := by
    intro j
    exact (halt (chosen j) (hchosenGood j)).2.1
  have huinj' : Function.Injective u := by
    simpa only [u] using huinj
  exact lambda_contradiction_of_injective_center
    ℓ C ((radius : ℝ) / n) hp c₀ hc₀ u huinj' huC huc y
    (by simpa only [hfloor] using hycRadius)
    (by intro j; simpa only [hfloor] using hyuRadius j) hLambda

theorem small_alphabet_power_bound
    (q dZero n : ℕ) (α η K γ : ℝ)
    (hα : 0 ≤ α) (hη : 0 < η) (hK : 0 ≤ K)
    (hq : (q : ℝ) < (2 : ℝ) ^ (α / η))
    (hdZero : dZero ≤ Nat.ceil (K * η * n))
    (hone : 1 ≤ η * n)
    (hbudget : α * (K + 1) ≤ γ / 4) :
    ((q ^ dZero : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((γ / 4) * n) := by
  have hceil := ceil_linear_bound K η n hK hη.le hone
  have hdZeroR : (dZero : ℝ) < (K + 1) * η * n := by
    have hcast : (dZero : ℝ) ≤
        (Nat.ceil (K * η * n) : ℝ) := by exact_mod_cast hdZero
    exact hcast.trans_lt hceil
  have hfactor : 0 ≤ α / η := div_nonneg hα hη.le
  have hexpMid : (α / η) * (dZero : ℝ) ≤
      α * (K + 1) * n := by
    calc
      (α / η) * (dZero : ℝ) ≤
          (α / η) * ((K + 1) * η * n) :=
        mul_le_mul_of_nonneg_left hdZeroR.le hfactor
      _ = α * (K + 1) * n := by
        field_simp [ne_of_gt hη]
  have hbudgetN : α * (K + 1) * (n : ℝ) ≤
      (γ / 4) * n :=
    mul_le_mul_of_nonneg_right hbudget (by positivity)
  have hexp : (α / η) * (dZero : ℝ) ≤ (γ / 4) * n :=
    hexpMid.trans hbudgetN
  have hqpow : (q : ℝ) ^ dZero ≤
      ((2 : ℝ) ^ (α / η)) ^ dZero :=
    pow_le_pow_left₀ (by positivity) hq.le dZero
  calc
    ((q ^ dZero : ℕ) : ℝ) = (q : ℝ) ^ dZero := by norm_num
    _ ≤ ((2 : ℝ) ^ (α / η)) ^ dZero := hqpow
    _ = (2 : ℝ) ^ ((α / η) * (dZero : ℝ)) :=
      (Real.rpow_mul_natCast (by norm_num) (α / η) dZero).symm
    _ ≤ (2 : ℝ) ^ ((γ / 4) * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- The radius at the mid-rate reference point, `ℓ/(ℓ+1) · (1 − ρ)/2`. Constants below are expressed
against it so they do not degrade as `η → 0`. -/
noncomputable def smallRadius (ℓ : ℕ) (ρ : ℝ) : ℝ :=
  (ℓ : ℝ) / (ℓ + 1) * ((1 - ρ) / 2)

/-- The cut-off below which `η` must lie for the barrier's parameters to fit. -/
noncomputable def barrierEtaCut (ℓ : ℕ) (R : ℝ) (B : ℕ) : ℝ :=
  min ((1 - R) / 2)
    (smallRadius ℓ R / (2 * (barrierK ℓ B + 1)))

theorem barrier_radius_window
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (η : ℝ) (hηpos : 0 < η) (hηcut : η < (1 - R) / 2) :
    0 < smallRadius ℓ R ∧
      smallRadius ℓ R ≤ relRadius ℓ R η ∧
      0 < relRadius ℓ R η ∧
      relRadius ℓ R η < (ℓ : ℝ) / (ℓ + 1) ∧
      relRadius ℓ R η < boostedRadius ℓ (relRadius ℓ R η) ∧
      boostedRadius ℓ (relRadius ℓ R η) < 1 := by
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hcoef : (0 : ℝ) < (ℓ : ℝ) / (ℓ + 1) := by positivity
  have hcoef1 : (ℓ : ℝ) / (ℓ + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hgapSmall : 0 < (1 - R) / 2 := by positivity
  have hsmall : 0 < smallRadius ℓ R := by
    unfold smallRadius
    exact mul_pos hcoef hgapSmall
  have hsmallLe : smallRadius ℓ R ≤ relRadius ℓ R η := by
    unfold smallRadius relRadius
    apply mul_le_mul_of_nonneg_left _ hcoef.le
    linarith
  have hηlt : η < 1 - R := by linarith
  have hp : 0 < relRadius ℓ R η :=
    relRadius_pos ℓ hℓpos R η hηlt
  have hgapOne : 1 - R - η < 1 := by linarith
  have hpcoef : relRadius ℓ R η < (ℓ : ℝ) / (ℓ + 1) := by
    unfold relRadius
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hgapOne hcoef
  have hpOne : relRadius ℓ R η < 1 := hpcoef.trans hcoef1
  have hboost : relRadius ℓ R η <
      boostedRadius ℓ (relRadius ℓ R η) :=
    boostedRadius_gt ℓ hℓpos _ hp
  have hpow : relRadius ℓ R η ^ ℓ ≤ relRadius ℓ R η :=
    pow_le_of_le_one hp.le hpOne.le (Nat.ne_of_gt hℓpos)
  have hdiv : relRadius ℓ R η ^ ℓ / (2 * ℓ) ≤
      relRadius ℓ R η / (2 * ℓ) :=
    div_le_div_of_nonneg_right hpow
      (show (0 : ℝ) ≤ 2 * ℓ by positivity)
  have hfacPos : (0 : ℝ) < 1 + 1 / (2 * ℓ) := by positivity
  have hcoefFac :
      ((ℓ : ℝ) / (ℓ + 1)) * (1 + 1 / (2 * ℓ)) < 1 := by
    field_simp [ne_of_gt hℓR]
    nlinarith
  have hboostOne : boostedRadius ℓ (relRadius ℓ R η) < 1 := by
    unfold boostedRadius
    calc
      relRadius ℓ R η + relRadius ℓ R η ^ ℓ / (2 * ℓ) ≤
          relRadius ℓ R η + relRadius ℓ R η / (2 * ℓ) :=
        add_le_add le_rfl hdiv
      _ = relRadius ℓ R η * (1 + 1 / (2 * ℓ)) := by ring
      _ < ((ℓ : ℝ) / (ℓ + 1)) * (1 + 1 / (2 * ℓ)) :=
        mul_lt_mul_of_pos_right hpcoef hfacPos
      _ < 1 := hcoefFac
  exact ⟨hsmall, hsmallLe, hp, hpcoef, hboost, hboostOne⟩

/-- The density `ξ = smallRadius^ℓ / (8ℓ)` — the gap the large-union family must beat. -/
noncomputable def barrierXiDensity (ℓ : ℕ) (R : ℝ) : ℝ :=
  smallRadius ℓ R ^ ℓ / (8 * ℓ)

/-- The union density `β = 1 − ξ` demanded of the large-union family. -/
noncomputable def barrierBetaDensity (ℓ : ℕ) (R : ℝ) : ℝ :=
  1 - barrierXiDensity ℓ R

theorem barrier_constant_bounds
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) :
    0 < barrierK ℓ B ∧
      0 < barrierEtaCut ℓ R B ∧
      barrierEtaCut ℓ R B ≤ (1 - R) / 2 ∧
      barrierEtaCut ℓ R B ≤
        smallRadius ℓ R / (2 * (barrierK ℓ B + 1)) ∧
      0 < barrierAlphaDensity R ∧
      barrierAlphaDensity R < barrierBetaDensity ℓ R ∧
      barrierBetaDensity ℓ R < 1 ∧
      0 < barrierXiDensity ℓ R := by
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hℓTwo : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hcoef : (0 : ℝ) < (ℓ : ℝ) / (ℓ + 1) := by positivity
  have hcoeflt : (ℓ : ℝ) / (ℓ + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hgap : 0 < (1 - R) / 2 := by linarith
  have hgaplt : (1 - R) / 2 < 1 := by linarith
  have hpMin : 0 < smallRadius ℓ R := by
    unfold smallRadius
    exact mul_pos hcoef hgap
  have hpMinlt : smallRadius ℓ R < 1 := by
    unfold smallRadius
    calc
      (ℓ : ℝ) / (ℓ + 1) * ((1 - R) / 2) <
          1 * ((1 - R) / 2) := mul_lt_mul_of_pos_right hcoeflt hgap
      _ < 1 := by simpa only [one_mul] using hgaplt
  have hK : 0 < barrierK ℓ B := by
    unfold barrierK
    positivity
  have hsecond :
      0 < smallRadius ℓ R / (2 * (barrierK ℓ B + 1)) := by
    positivity
  have hEta : 0 < barrierEtaCut ℓ R B := by
    unfold barrierEtaCut
    exact lt_min hgap hsecond
  have hAlpha : 0 < barrierAlphaDensity R := by
    unfold barrierAlphaDensity
    positivity
  have hXi : 0 < barrierXiDensity ℓ R := by
    unfold barrierXiDensity
    positivity
  have hpow : smallRadius ℓ R ^ ℓ ≤ smallRadius ℓ R :=
    pow_le_of_le_one hpMin.le hpMinlt.le (Nat.ne_of_gt hℓpos)
  have hXiHalf : barrierXiDensity ℓ R < (1 : ℝ) / 2 := by
    unfold barrierXiDensity
    have hden : (0 : ℝ) < 8 * ℓ := by positivity
    rw [div_lt_iff₀ hden]
    have hpOne : smallRadius ℓ R ^ ℓ < 1 := hpow.trans_lt hpMinlt
    nlinarith
  have hAlphaHalf : barrierAlphaDensity R < (1 : ℝ) / 2 := by
    unfold barrierAlphaDensity
    linarith
  have hAlphaBeta :
      barrierAlphaDensity R < barrierBetaDensity ℓ R := by
    unfold barrierBetaDensity
    linarith
  have hBetaOne : barrierBetaDensity ℓ R < 1 := by
    unfold barrierBetaDensity
    linarith
  exact ⟨hK, hEta, min_le_left _ _, min_le_right _ _, hAlpha,
    hAlphaBeta, hBetaOne, hXi⟩

theorem barrier_density_real_gaps
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < barrierEtaCut ℓ R B) :
    let p := relRadius ℓ R η
    let _p₀ := smallRadius ℓ R
    let ξ := barrierXiDensity ℓ R
    let β := barrierBetaDensity ℓ R
    R < β * (1 - p) ∧
      1 - boostedRadius ℓ p + 3 * ξ ≤ β * (1 - p) := by
  dsimp only
  let p := relRadius ℓ R η
  let p₀ := smallRadius ℓ R
  let ξ := barrierXiDensity ℓ R
  let β := barrierBetaDensity ℓ R
  change R < β * (1 - p) ∧
    1 - boostedRadius ℓ p + 3 * ξ ≤ β * (1 - p)
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  rcases barrier_constant_bounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBeta, hXi⟩
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases barrier_radius_window ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hp₀, hp₀le, hp, hpCoef, hBoost, hBoostOne⟩
  change 0 < p₀ at hp₀
  change p₀ ≤ p at hp₀le
  change 0 < p at hp
  change p < boostedRadius ℓ p at hBoost
  have hpOne : p < 1 := hBoost.trans hBoostOne
  have hp₀One : p₀ < 1 := hp₀le.trans_lt hpOne
  change 0 < ξ at hXi
  have hbalance : R + p + p / (ℓ : ℝ) = 1 - η := by
    simpa only [p] using relRadius_balance ℓ hℓpos R η
  have hp₀pow : p₀ ^ ℓ ≤ p₀ :=
    pow_le_of_le_one hp₀.le hp₀One.le (Nat.ne_of_gt hℓpos)
  have hpowLeP : p₀ ^ ℓ ≤ p := hp₀pow.trans hp₀le
  have hxiLe : ξ ≤ p / (8 * (ℓ : ℝ)) := by
    dsimp only [ξ, p₀, barrierXiDensity]
    exact div_le_div_of_nonneg_right hpowLeP (by positivity)
  have hpDivStrict : p / (8 * (ℓ : ℝ)) < p / (ℓ : ℝ) := by
    field_simp [ne_of_gt hℓR]
    nlinarith
  have hxiLt : ξ < p / (ℓ : ℝ) := hxiLe.trans_lt hpDivStrict
  have hxiMul : ξ * (1 - p) ≤ ξ := by
    rw [mul_sub, mul_one]
    exact sub_le_self _ (mul_nonneg hXi.le hp.le)
  have hxiMulLt : ξ * (1 - p) < p / (ℓ : ℝ) :=
    hxiMul.trans_lt hxiLt
  have hgapOne :
      β * (1 - p) - R =
        η + p / (ℓ : ℝ) - ξ * (1 - p) := by
    dsimp only [β, barrierBetaDensity]
    linear_combination -hbalance
  have hpowMono : p₀ ^ ℓ ≤ p ^ ℓ :=
    pow_le_pow_left₀ hp₀.le hp₀le ℓ
  have hfourXi : 4 * ξ ≤ p ^ ℓ / (2 * (ℓ : ℝ)) := by
    calc
      4 * ξ = p₀ ^ ℓ / (2 * (ℓ : ℝ)) := by
        dsimp only [ξ, barrierXiDensity]
        ring
      _ ≤ p ^ ℓ / (2 * (ℓ : ℝ)) :=
        div_le_div_of_nonneg_right hpowMono (by positivity)
  have hxiFour : ξ * (4 - p) ≤ p ^ ℓ / (2 * (ℓ : ℝ)) := by
    calc
      ξ * (4 - p) ≤ ξ * 4 :=
        mul_le_mul_of_nonneg_left (by linarith) hXi.le
      _ = 4 * ξ := by ring
      _ ≤ p ^ ℓ / (2 * (ℓ : ℝ)) := hfourXi
  have hgapTwo :
      β * (1 - p) - (1 - boostedRadius ℓ p + 3 * ξ) =
        p ^ ℓ / (2 * (ℓ : ℝ)) - ξ * (4 - p) := by
    dsimp only [β, barrierBetaDensity, boostedRadius]
    ring
  constructor
  · apply sub_pos.mp
    rw [hgapOne]
    linarith
  · apply sub_nonneg.mp
    rw [hgapTwo]
    exact sub_nonneg.mpr hxiFour

/-- The length past which the local neighbourhood bound applies, `⌈8ℓ / smallRadius^ℓ⌉`. -/
noncomputable def localLengthThreshold (ℓ : ℕ) (ρ : ℝ) : ℕ :=
  Nat.ceil (8 * (ℓ : ℝ) / (smallRadius ℓ ρ) ^ ℓ)

/-- The local neighbourhood bound's value, `ℓ + ⌈4ℓ² / smallRadius⌉`: how many codewords can sit
within the boosted radius of one codeword when the list size is at most `ℓ`. -/
noncomputable def neighborhoodCap (ℓ : ℕ) (ρ : ℝ) : ℕ :=
  ℓ + Nat.ceil (4 * (ℓ : ℝ) ^ 2 / smallRadius ℓ ρ)

theorem rounded_barrier_basic_bounds
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < barrierEtaCut ℓ R B) (n : ℕ)
    (hn : roundedBarrierBasicThreshold R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
      d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
      d.boosted ≤ n ∧ d.radius ≤ n := by
  dsimp only [roundedBarrierData]
  rcases barrier_constant_bounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBeta, hXi⟩
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases barrier_radius_window ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hpMin, hpMinLe, hp, hpCoef, hBoost, hBoostOne⟩
  have hone : 1 ≤ η * (n : ℝ) :=
    eta_times_length_one η n hηpos hlen
  have hnR : (0 : ℝ) < n := by
    by_contra hnot
    have hnle : (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hprod : η * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hηpos.le hnle
    linarith
  have hrateCeil : (((B + 1 : ℕ) : ℝ) / R) ≤ (n : ℝ) := by
    apply (Nat.ceil_le).mp
    simpa only [roundedBarrierBasicThreshold] using hn
  have hrateReal : ((B + 1 : ℕ) : ℝ) ≤ R * n := by
    have h := (div_le_iff₀ hRpos).mp hrateCeil
    simpa only [mul_comm] using h
  have hrateFloor : B + 1 ≤ Nat.floor (R * n) := by
    exact (Nat.le_floor_iff (mul_nonneg hRpos.le hnR.le)).2 hrateReal
  have hden : 0 < 2 * (barrierK ℓ B + 1) := by positivity
  have hηSecondStrict :
      η < smallRadius ℓ R /
        (2 * (barrierK ℓ B + 1)) := hηcut.trans_le hEtaSecond
  have hcross := (lt_div_iff₀ hden).mp hηSecondStrict
  have hKeta :
      (barrierK ℓ B + 1) * η < smallRadius ℓ R / 2 := by
    nlinarith only [hcross]
  have hKetaN :
      (barrierK ℓ B + 1) * η * n <
        smallRadius ℓ R / 2 * n :=
    mul_lt_mul_of_pos_right hKeta hnR
  have hhalfP : smallRadius ℓ R / 2 < relRadius ℓ R η := by
    nlinarith only [hpMin, hpMinLe]
  have hhalfPN : smallRadius ℓ R / 2 * n <
      relRadius ℓ R η * n :=
    mul_lt_mul_of_pos_right hhalfP hnR
  have hceil := ceil_linear_bound
    (barrierK ℓ B) η n hK.le hηpos.le hone
  have hdZero : Nat.ceil (barrierK ℓ B * η * n) ≤
      Nat.floor (relRadius ℓ R η * n) := by
    apply (Nat.le_floor_iff (mul_nonneg hp.le hnR.le)).2
    exact (hceil.trans (hKetaN.trans hhalfPN)).le
  have hBoostPosReal :
      0 < boostedRadius ℓ (relRadius ℓ R η) * n :=
    mul_pos (hp.trans hBoost) hnR
  have hBoostPos :
      0 < Nat.ceil (boostedRadius ℓ (relRadius ℓ R η) * n) :=
    (Nat.ceil_pos).2 hBoostPosReal
  have hBoostLe :
      Nat.ceil (boostedRadius ℓ (relRadius ℓ R η) * n) ≤ n := by
    apply (Nat.ceil_le).2
    have h := mul_le_mul_of_nonneg_right hBoostOne.le hnR.le
    simpa only [one_mul] using h
  have hCoefOne : (ℓ : ℝ) / (ℓ + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hpOne : relRadius ℓ R η < 1 := hpCoef.trans hCoefOne
  have hRadiusLe : Nat.floor (relRadius ℓ R η * n) ≤ n := by
    have hmul : relRadius ℓ R η * n ≤ (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hpOne.le hnR.le
      simpa only [one_mul] using h
    have hfloor := Nat.floor_mono hmul
    simpa only [Nat.floor_natCast] using hfloor
  exact ⟨hone, hrateFloor, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩

/-- The length threshold at which every density estimate for the rounded parameters holds. -/
noncomputable def roundedBarrierDensityThreshold
    (ℓ : ℕ) (R : ℝ) (B : ℕ) : ℕ :=
  max (roundedBarrierBasicThreshold R B)
    (max
      (Nat.ceil (((2 * (B + 2) : ℕ) : ℝ) / R))
      (Nat.ceil (1 / (3 * barrierXiDensity ℓ R))))

theorem rounded_barrier_density_threshold_bounds
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (n : ℕ)
    (hn : roundedBarrierDensityThreshold ℓ R B ≤ n) :
    roundedBarrierBasicThreshold R B ≤ n ∧
      ((2 * (B + 2) : ℕ) : ℝ) ≤ R * n ∧
      1 ≤ 3 * barrierXiDensity ℓ R * n := by
  have hBasic : roundedBarrierBasicThreshold R B ≤ n := by
    dsimp only [roundedBarrierDensityThreshold] at hn
    omega
  have hRateCeil :
      Nat.ceil (((2 * (B + 2) : ℕ) : ℝ) / R) ≤ n := by
    dsimp only [roundedBarrierDensityThreshold] at hn
    omega
  have hRateDiv : ((2 * (B + 2) : ℕ) : ℝ) / R ≤ n :=
    (Nat.ceil_le).mp hRateCeil
  have hRate : ((2 * (B + 2) : ℕ) : ℝ) ≤ R * n := by
    have h := (div_le_iff₀ hRpos).mp hRateDiv
    simpa only [mul_comm] using h
  rcases barrier_constant_bounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBeta, hXi⟩
  have hXiCeil :
      Nat.ceil (1 / (3 * barrierXiDensity ℓ R)) ≤ n := by
    dsimp only [roundedBarrierDensityThreshold] at hn
    omega
  have hXiDiv :
      1 / (3 * barrierXiDensity ℓ R) ≤ (n : ℝ) :=
    (Nat.ceil_le).mp hXiCeil
  have hden : 0 < 3 * barrierXiDensity ℓ R := by positivity
  have hXiBound : 1 ≤ 3 * barrierXiDensity ℓ R * n := by
    have h := (div_le_iff₀ hden).mp hXiDiv
    simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using h
  exact ⟨hBasic, hRate, hXiBound⟩

theorem rounded_barrier_lower_family_density
    (ℓ : ℕ) (_hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (_hB : 0 < B) (η : ℝ) (_hηpos : 0 < η)
    (_hηcut : η < barrierEtaCut ℓ R B) (n : ℕ)
    (hn : roundedBarrierDensityThreshold ℓ R B ≤ n)
    (_hlen : 1 / η ≤ (n : ℝ)) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    Nat.floor (barrierAlphaDensity R * d.unused) ≤ d.aFamily := by
  let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
  change Nat.floor (barrierAlphaDensity R * d.unused) ≤ d.aFamily
  have hRateCeil :
      Nat.ceil (((2 * (B + 2) : ℕ) : ℝ) / R) ≤ n := by
    dsimp only [roundedBarrierDensityThreshold] at hn
    omega
  have hRateDiv : (((2 * (B + 2) : ℕ) : ℝ) / R) ≤ (n : ℝ) :=
    (Nat.ceil_le).mp hRateCeil
  have hRate : ((2 * (B + 2) : ℕ) : ℝ) ≤ R * n := by
    have h := (div_le_iff₀ hRpos).mp hRateDiv
    simpa only [mul_comm] using h
  have hmle : d.unused ≤ n := by
    dsimp only [d, roundedBarrierData]
    exact Nat.sub_le _ _
  have hmleR : (d.unused : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmle
  have hhalf :
      (R / 2) * (d.unused : ℝ) + (B + 1 : ℕ) ≤ R * n := by
    have hmhalf : (R / 2) * (d.unused : ℝ) ≤ (R / 2) * n :=
      mul_le_mul_of_nonneg_left hmleR (by positivity)
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hRate ⊢
    nlinarith
  have htermNonneg : 0 ≤ (R / 2) * (d.unused : ℝ) := by positivity
  have hfloorTerm :
      (Nat.floor ((R / 2) * (d.unused : ℝ)) : ℝ) ≤
        (R / 2) * (d.unused : ℝ) := Nat.floor_le htermNonneg
  have hRn : 0 ≤ R * (n : ℝ) := by positivity
  have hsumReal :
      ((Nat.floor ((R / 2) * (d.unused : ℝ)) + (B + 1) : ℕ) : ℝ) ≤
        R * n := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hhalf ⊢
    linarith
  have hsum :
      Nat.floor ((R / 2) * (d.unused : ℝ)) + (B + 1) ≤
        Nat.floor (R * n) :=
    (Nat.le_floor_iff hRn).2 hsumReal
  have hfamily : d.aFamily = Nat.floor (R * n) - (B + 1) := by
    rfl
  rw [hfamily]
  unfold barrierAlphaDensity
  omega

theorem rounded_barrier_other_codeword_bound
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < barrierEtaCut ℓ R B) (n : ℕ)
    (hn : roundedBarrierBasicThreshold R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    n - d.dZero - d.dOne - d.aFamily ≤ d.radius := by
  have hbasic := rounded_barrier_basic_bounds
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  dsimp only at hbasic ⊢
  exact rounded_barrier_other_codeword_bound_core
    ℓ hℓ R η B n hbasic.1 hbasic.2.1 hbasic.2.2.1

theorem barrier_parameters_exist
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < barrierEtaCut ℓ R B) (n W : ℕ) (hW : 0 < W)
    (hn : roundedBarrierBasicThreshold R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    ∃ params : BarrierParameters ℓ n d.radius d.boosted,
      0 < params.W ∧ params.W = W ∧
      params.aFamily = d.aFamily ∧ params.aUnion = d.aUnion ∧
      params.dZero = d.dZero ∧ params.dOne = d.dOne := by
  let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
  change ∃ params : BarrierParameters ℓ n d.radius d.boosted,
    0 < params.W ∧ params.W = W ∧
    params.aFamily = d.aFamily ∧ params.aUnion = d.aUnion ∧
    params.dZero = d.dZero ∧ params.dOne = d.dOne
  have hbasic :
      1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
        d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
        d.boosted ≤ n ∧ d.radius ≤ n := by
    simpa only [d] using rounded_barrier_basic_bounds
      ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  rcases hbasic with
    ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
  have hℓpos : 0 < ℓ := by omega
  have hquot := nat_quotient_window
    ℓ d.radius d.dZero n hℓpos hdZero hRadiusLe
  have hcenter : d.dZero + ℓ * d.dOne ≤ d.radius := by
    simpa only [d, roundedBarrierData] using hquot.1
  have hother : n - d.dZero - d.dOne - d.aFamily ≤ d.radius := by
    simpa only [d] using rounded_barrier_other_codeword_bound
      ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  have hrepeated : n - d.aUnion < d.boosted := by
    dsimp only [d, roundedBarrierData] at hBoostPos hBoostLe ⊢
    omega
  let params : BarrierParameters ℓ n d.radius d.boosted :=
    { aFamily := d.aFamily
      aUnion := d.aUnion
      dZero := d.dZero
      dOne := d.dOne
      W := W
      center_block_bound := hcenter
      other_codeword_bound := hother
      repeated_codeword_contradiction := hrepeated }
  refine ⟨params, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [params] using hW
  all_goals rfl

theorem rounded_barrier_quotient_bounds
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B n : ℕ) (η : ℝ) (hηpos : 0 < η)
    (hηhalf : η < (1 - R) / 2)
    (hdZero :
      (roundedBarrierData ℓ R η (barrierK ℓ B) B n).dZero ≤
        (roundedBarrierData ℓ R η (barrierK ℓ B) B n).radius)
    (hradius :
      (roundedBarrierData ℓ R η (barrierK ℓ B) B n).radius ≤ n) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    d.used ≤ d.radius ∧ d.radius < d.used + ℓ ∧
      n - d.radius ≤ d.unused ∧
      d.unused ≤ n - d.radius + (ℓ - 1) ∧
      Nat.floor (R * n) ≤ d.unused ∧ d.aFamily ≤ d.unused ∧
      n ≤ (ℓ + 1) * d.unused := by
  dsimp only [roundedBarrierData] at hdZero hradius ⊢
  have hℓpos : 0 < ℓ := by omega
  by_cases hnzero : n = 0
  · subst n
    simp [Nat.zero_div, hℓpos]
  have hn : 0 < n := Nat.pos_of_ne_zero hnzero
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  rcases nat_quotient_window ℓ
      (Nat.floor (relRadius ℓ R η * n))
      (Nat.ceil (barrierK ℓ B * η * n)) n hℓpos hdZero hradius with
    ⟨hused, hrUsed, hmLower, hmUpper⟩
  rcases barrier_radius_window ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hpMin, hpMinLe, hp, hpCoef, hBoost, hBoostOne⟩
  have hbalance := relRadius_balance ℓ hℓpos R η
  have hpDiv : 0 < relRadius ℓ R η / (ℓ : ℝ) :=
    div_pos hp hℓR
  have hRp : R + relRadius ℓ R η < 1 := by
    linarith only [hbalance, hpDiv, hηpos]
  have hRfloor : (Nat.floor (R * n) : ℝ) ≤ R * n :=
    Nat.floor_le (mul_nonneg hRpos.le hnR.le)
  have hPfloor : (Nat.floor (relRadius ℓ R η * n) : ℝ) ≤
      relRadius ℓ R η * n :=
    Nat.floor_le (mul_nonneg hp.le hnR.le)
  have hRpN : (R + relRadius ℓ R η) * n < (n : ℝ) := by
    have h := mul_lt_mul_of_pos_right hRp hnR
    simpa only [one_mul] using h
  have hsumReal :
      (Nat.floor (R * n) : ℝ) +
          Nat.floor (relRadius ℓ R η * n) < n := by
    calc
      (Nat.floor (R * n) : ℝ) +
          Nat.floor (relRadius ℓ R η * n) ≤
          R * n + relRadius ℓ R η * n := add_le_add hRfloor hPfloor
      _ = (R + relRadius ℓ R η) * n := by ring
      _ < n := hRpN
  have hsumNat :
      Nat.floor (R * n) + Nat.floor (relRadius ℓ R η * n) ≤ n := by
    exact_mod_cast hsumReal.le
  have hfloorM : Nat.floor (R * n) ≤
      n - (Nat.ceil (barrierK ℓ B * η * n) +
        ℓ * ((Nat.floor (relRadius ℓ R η * n) -
          Nat.ceil (barrierK ℓ B * η * n)) / ℓ)) := by
    omega
  have haM : Nat.floor (R * n) - (B + 1) ≤
      n - (Nat.ceil (barrierK ℓ B * η * n) +
        ℓ * ((Nat.floor (relRadius ℓ R η * n) -
          Nat.ceil (barrierK ℓ B * η * n)) / ℓ)) := by
    exact (Nat.sub_le _ _).trans hfloorM
  have hden : (0 : ℝ) < ℓ + 1 := by positivity
  have hpCross : relRadius ℓ R η * ((ℓ : ℝ) + 1) < ℓ := by
    exact (lt_div_iff₀ hden).mp hpCoef
  have hpCrossN :
      (relRadius ℓ R η * ((ℓ : ℝ) + 1)) * n < (ℓ : ℝ) * n :=
    mul_lt_mul_of_pos_right hpCross hnR
  have hscaledReal :
      ((ℓ + 1 : ℕ) : ℝ) * Nat.floor (relRadius ℓ R η * n) <
        (ℓ : ℝ) * n := by
    calc
      ((ℓ + 1 : ℕ) : ℝ) * Nat.floor (relRadius ℓ R η * n) ≤
          ((ℓ : ℝ) + 1) * (relRadius ℓ R η * n) := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        exact mul_le_mul_of_nonneg_left hPfloor (by positivity)
      _ = (relRadius ℓ R η * ((ℓ : ℝ) + 1)) * n := by ring
      _ < (ℓ : ℝ) * n := hpCrossN
  have hnLowerReal : (n : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) *
      (n - Nat.floor (relRadius ℓ R η * n) : ℕ) := by
    rw [Nat.cast_sub hradius]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hnLower : n ≤ (ℓ + 1) *
      (n - Nat.floor (relRadius ℓ R η * n)) := by
    exact_mod_cast hnLowerReal
  have hnM : n ≤ (ℓ + 1) *
      (n - (Nat.ceil (barrierK ℓ B * η * n) +
        ℓ * ((Nat.floor (relRadius ℓ R η * n) -
          Nat.ceil (barrierK ℓ B * η * n)) / ℓ))) := by
    exact hnLower.trans
      (Nat.mul_le_mul_left (ℓ + 1) hmLower)
  exact ⟨hused, hrUsed, hmLower, hmUpper, hfloorM, haM, hnM⟩

private theorem one_sub_mul_le_nat_sub
    (p : ℝ) (n radius : ℕ) (hRadiusLe : radius ≤ n)
    (hRadiusFloor : (radius : ℝ) ≤ p * n) :
    (1 - p) * (n : ℝ) ≤ (n - radius : ℕ) := by
  rw [Nat.cast_sub hRadiusLe]
  calc
    (1 - p) * (n : ℝ) = (n : ℝ) - p * n := by ring
    _ ≤ (n : ℝ) - radius := sub_le_sub_left hRadiusFloor _

theorem rounded_barrier_upper_family_density
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < barrierEtaCut ℓ R B) (n : ℕ)
    (hn : roundedBarrierDensityThreshold ℓ R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    d.aFamily < Nat.ceil (barrierBetaDensity ℓ R * d.unused) := by
  let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
  let p := relRadius ℓ R η
  let β := barrierBetaDensity ℓ R
  change d.aFamily < Nat.ceil (β * d.unused)
  rcases rounded_barrier_density_threshold_bounds
      ℓ hℓ R hRpos hRlt B hB n hn with
    ⟨hBasicThreshold, hRateBudget, hXiBudget⟩
  have hbasic := rounded_barrier_basic_bounds
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hBasicThreshold hlen
  change 1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
      d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
      d.boosted ≤ n ∧ d.radius ≤ n at hbasic
  rcases hbasic with
    ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
  rcases barrier_constant_bounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBetaOne, hXi⟩
  have hBetaPos : 0 < β := by
    change 0 < barrierBetaDensity ℓ R
    exact hAlpha.trans hAlphaBeta
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases rounded_barrier_quotient_bounds
      ℓ hℓ R hRpos hRlt B n η hηpos hηhalf
      (by simpa only [d] using hdZero)
      (by simpa only [d] using hRadiusLe) with
    ⟨hUsed, hRadiusUsed, hmLower, hmUpper, hFloorM, haM, hnM⟩
  rcases barrier_density_real_gaps
      ℓ hℓ R hRpos hRlt B hB η hηpos hηcut with
    ⟨hRateGap, hUnionGap⟩
  change R < β * (1 - p) at hRateGap
  rcases barrier_radius_window
      ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hpMin, hpMinLe, hp, hpCoef, hBoost, hBoostOne⟩
  change 0 < p at hp
  have hnR : (0 : ℝ) < n := by
    by_contra hnot
    have hnle : (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hprod : η * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hηpos.le hnle
    linarith
  have hAFloor : d.aFamily ≤ Nat.floor (R * n) := by
    dsimp only [d, roundedBarrierData]
    exact Nat.sub_le _ _
  have hAReal : (d.aFamily : ℝ) ≤ R * n := by
    calc
      (d.aFamily : ℝ) ≤ (Nat.floor (R * n) : ℝ) := by
        exact_mod_cast hAFloor
      _ ≤ R * n := Nat.floor_le (by positivity)
  have hRadiusFloor : (d.radius : ℝ) ≤ p * n := by
    dsimp only [d, roundedBarrierData, p]
    exact Nat.floor_le (by positivity)
  have hOneP : (1 - p) * (n : ℝ) ≤ (n - d.radius : ℕ) :=
    one_sub_mul_le_nat_sub p n d.radius hRadiusLe hRadiusFloor
  have hmLowerR : ((n - d.radius : ℕ) : ℝ) ≤ d.unused := by
    exact_mod_cast hmLower
  have hGapN : R * (n : ℝ) < β * ((1 - p) * n) := by
    calc
      R * (n : ℝ) < (β * (1 - p)) * n :=
        mul_lt_mul_of_pos_right hRateGap hnR
      _ = β * ((1 - p) * n) := by ring
  have hBetaSub : β * ((1 - p) * n) ≤ β * d.unused := by
    apply mul_le_mul_of_nonneg_left _ hBetaPos.le
    exact hOneP.trans hmLowerR
  apply (Nat.lt_ceil).2
  exact hAReal.trans_lt (hGapN.trans_le hBetaSub)

theorem rounded_barrier_upper_union_density
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < barrierEtaCut ℓ R B) (n : ℕ)
    (hn : roundedBarrierDensityThreshold ℓ R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    d.aUnion ≤ Nat.ceil (barrierBetaDensity ℓ R * d.unused) := by
  let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
  let p := relRadius ℓ R η
  let p' := boostedRadius ℓ p
  let ξ := barrierXiDensity ℓ R
  let β := barrierBetaDensity ℓ R
  change d.aUnion ≤ Nat.ceil (β * d.unused)
  rcases rounded_barrier_density_threshold_bounds
      ℓ hℓ R hRpos hRlt B hB n hn with
    ⟨hBasicThreshold, hRateBudget, hXiBudget⟩
  change 1 ≤ 3 * ξ * n at hXiBudget
  have hbasic := rounded_barrier_basic_bounds
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hBasicThreshold hlen
  change 1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
      d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
      d.boosted ≤ n ∧ d.radius ≤ n at hbasic
  rcases hbasic with
    ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
  rcases barrier_constant_bounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBetaOne, hXi⟩
  have hBetaPos : 0 < β := by
    change 0 < barrierBetaDensity ℓ R
    exact hAlpha.trans hAlphaBeta
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases rounded_barrier_quotient_bounds
      ℓ hℓ R hRpos hRlt B n η hηpos hηhalf
      (by simpa only [d] using hdZero)
      (by simpa only [d] using hRadiusLe) with
    ⟨hUsed, hRadiusUsed, hmLower, hmUpper, hFloorM, haM, hnM⟩
  rcases barrier_density_real_gaps
      ℓ hℓ R hRpos hRlt B hB η hηpos hηcut with
    ⟨hRateGap, hUnionGap⟩
  change 1 - p' + 3 * ξ ≤ β * (1 - p) at hUnionGap
  rcases barrier_radius_window
      ℓ hℓ R hRpos hRlt η hηpos hηhalf with
    ⟨hpMin, hpMinLe, hp, hpCoef, hBoost, hBoostOne⟩
  change 0 < p at hp
  have hnR : (0 : ℝ) < n := by
    by_contra hnot
    have hnle : (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hprod : η * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hηpos.le hnle
    linarith
  have hBoostLower : p' * (n : ℝ) ≤ (d.boosted : ℝ) := by
    dsimp only [d, roundedBarrierData, p', p]
    exact Nat.le_ceil _
  have hBoostLeSucc : d.boosted ≤ n + 1 := hBoostLe.trans (Nat.le_succ n)
  have hBoostLeSucc' :
      Nat.ceil (boostedRadius ℓ (relRadius ℓ R η) * n) ≤ n + 1 := by
    simpa only [d, roundedBarrierData] using hBoostLeSucc
  have hAUnionCast : (d.aUnion : ℝ) =
      (n : ℝ) + 1 - d.boosted := by
    dsimp only [d, roundedBarrierData]
    rw [Nat.cast_sub hBoostLeSucc']
    norm_num
  have hUnionBase : (d.aUnion : ℝ) ≤ (1 - p') * n + 1 := by
    rw [hAUnionCast]
    calc
      (n : ℝ) + 1 - d.boosted ≤ (n : ℝ) + 1 - p' * n :=
        sub_le_sub_left hBoostLower _
      _ = (1 - p') * n + 1 := by ring
  have hUnionBudget : (1 - p') * n + 1 ≤
      (1 - p' + 3 * ξ) * n := by
    calc
      (1 - p') * n + 1 ≤ (1 - p') * n + 3 * ξ * n :=
        add_le_add_right hXiBudget _
      _ = (1 - p' + 3 * ξ) * n := by ring
  have hGapN : (1 - p' + 3 * ξ) * n ≤
      β * ((1 - p) * n) := by
    calc
      (1 - p' + 3 * ξ) * (n : ℝ) ≤ (β * (1 - p)) * n :=
        mul_le_mul_of_nonneg_right hUnionGap hnR.le
      _ = β * ((1 - p) * n) := by ring
  have hRadiusFloor : (d.radius : ℝ) ≤ p * n := by
    dsimp only [d, roundedBarrierData, p]
    exact Nat.floor_le (by positivity)
  have hOneP : (1 - p) * (n : ℝ) ≤ (n - d.radius : ℕ) :=
    one_sub_mul_le_nat_sub p n d.radius hRadiusLe hRadiusFloor
  have hmLowerR : ((n - d.radius : ℕ) : ℝ) ≤ d.unused := by
    exact_mod_cast hmLower
  have hBetaSub : β * ((1 - p) * n) ≤ β * d.unused := by
    apply mul_le_mul_of_nonneg_left _ hBetaPos.le
    exact hOneP.trans hmLowerR
  have hUnionReal : (d.aUnion : ℝ) ≤ β * d.unused :=
    hUnionBase.trans (hUnionBudget.trans (hGapN.trans hBetaSub))
  have hCeilReal : (d.aUnion : ℝ) ≤
      (Nat.ceil (β * d.unused) : ℝ) :=
    hUnionReal.trans (Nat.le_ceil _)
  exact_mod_cast hCeilReal

theorem rounded_barrier_density_window
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (R : ℝ) (hRpos : 0 < R) (hRlt : R < 1)
    (B : ℕ) (hB : 0 < B) (η : ℝ) (hηpos : 0 < η)
    (hηcut : η < barrierEtaCut ℓ R B) (n : ℕ)
    (hn : roundedBarrierDensityThreshold ℓ R B ≤ n)
    (hlen : 1 / η ≤ (n : ℝ)) :
    let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
    Nat.floor (barrierAlphaDensity R * d.unused) ≤ d.aFamily ∧
      d.aFamily < Nat.ceil (barrierBetaDensity ℓ R * d.unused) ∧
      d.aUnion ≤ Nat.ceil (barrierBetaDensity ℓ R * d.unused) ∧
      d.aFamily ≤ d.unused := by
  let d := roundedBarrierData ℓ R η (barrierK ℓ B) B n
  change Nat.floor (barrierAlphaDensity R * d.unused) ≤ d.aFamily ∧
    d.aFamily < Nat.ceil (barrierBetaDensity ℓ R * d.unused) ∧
    d.aUnion ≤ Nat.ceil (barrierBetaDensity ℓ R * d.unused) ∧
    d.aFamily ≤ d.unused
  have hLower := rounded_barrier_lower_family_density
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  change Nat.floor (barrierAlphaDensity R * d.unused) ≤
    d.aFamily at hLower
  have hUpperFamily := rounded_barrier_upper_family_density
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  change d.aFamily < Nat.ceil
    (barrierBetaDensity ℓ R * d.unused) at hUpperFamily
  have hUpperUnion := rounded_barrier_upper_union_density
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hn hlen
  change d.aUnion ≤ Nat.ceil
    (barrierBetaDensity ℓ R * d.unused) at hUpperUnion
  rcases rounded_barrier_density_threshold_bounds
      ℓ hℓ R hRpos hRlt B hB n hn with
    ⟨hBasicThreshold, hRateBudget, hXiBudget⟩
  have hbasic := rounded_barrier_basic_bounds
    ℓ hℓ R hRpos hRlt B hB η hηpos hηcut n hBasicThreshold hlen
  change 1 ≤ η * n ∧ B + 1 ≤ Nat.floor (R * n) ∧
      d.dZero ≤ d.radius ∧ 0 < d.boosted ∧
      d.boosted ≤ n ∧ d.radius ≤ n at hbasic
  rcases hbasic with
    ⟨hone, hrate, hdZero, hBoostPos, hBoostLe, hRadiusLe⟩
  rcases barrier_constant_bounds ℓ hℓ R hRpos hRlt B hB with
    ⟨hK, hEta, hEtaHalf, hEtaSecond, hAlpha, hAlphaBeta,
      hBetaOne, hXi⟩
  have hηhalf : η < (1 - R) / 2 := hηcut.trans_le hEtaHalf
  rcases rounded_barrier_quotient_bounds
      ℓ hℓ R hRpos hRlt B n η hηpos hηhalf
      (by simpa only [d] using hdZero)
      (by simpa only [d] using hRadiusLe) with
    ⟨hUsed, hRadiusUsed, hmLower, hmUpper, hFloorM, haM, hnM⟩
  exact ⟨hLower, hUpperFamily, hUpperUnion, haM⟩

end LargeAlphabetBarrier

end CodingTheory

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Mathlib.InformationTheory.Hamming
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Tactic.Qify

import ArkLib.Data.Fin.Basic

/-!
  # Basics of Coding Theory

  We define a general code `C` to be a subset of `n → R` for some finite index set `n` and some
  target type `R`.

  We can then specialize this notion to various settings. For `[CommSemiring R]`, we define a linear
  code to be a linear subspace of `n → R`. We also define the notion of generator matrix and
  (parity) check matrix.

  ## Main Definitions

  - `dist C`: The Hamming distance of a code `C`, defined as the infimum (in `ℕ∞`) of the
    Hamming distances between any two distinct elements of `C`. This is noncomputable.

  - `dist' C`: A computable version of `dist C`, assuming `C` is a `Fintype`.

  We define the block length, rate, and distance of `C`. We prove simple properties of linear codes
  such as the singleton bound.
-/


variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code

-- Notation for Hamming distance
notation "Δ₀(" u ", " v ")" => hammingDist u v

notation "‖" u "‖₀" => hammingNorm u

/-- The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct
  elements of the code.
cd
We formalize this as the infimum `sInf` over all `d : ℕ` such that there exist `u v : n → R` in the
code with `u ≠ v` and `hammingDist u v ≤ d`. If none exists, then we define the distance to be `0`.
-/
noncomputable def dist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ Δ₀( u, v ) ≤ d}

-- TODO: rewrite this file using existing `(e)infsep` definitions

instance : EDist (n → R) where
  edist := fun u v => hammingDist u v

instance : Dist (n → R) where
  dist := fun u v => hammingDist u v

noncomputable def eCodeDistNew (C : Set (n → R)) : ENNReal := C.einfsep

noncomputable def codeDistNew (C : Set (n → R)) : ℝ := C.infsep

notation "‖" C "‖₀" => dist C

/-- The distance from a vector `u` to a code `C` is the minimum Hamming distance between `u`
and any element of `C`. -/
noncomputable def distFromCode (u : n → R) (C : Set (n → R)) : ℕ∞ :=
  sInf {d | ∃ v ∈ C, hammingDist u v ≤ d}

notation "Δ₀(" u ", " C ")" => distFromCode u C

noncomputable def minDist (C : Set (n → R)) : ℕ :=
  sInf {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}

@[simp]
theorem dist_empty : ‖ (∅ : Set (n → R) ) ‖₀ = 0 := by simp [dist]

@[simp]
theorem dist_subsingleton {C : Set (n → R)} [Subsingleton C] : ‖C‖₀ = 0 := by
  simp only [Code.dist]
  have {d : ℕ} : (∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d) = False := by
    have h := @Subsingleton.allEq C _
    simp_all; intro a ha b hb hab
    have hEq : a = b := h a ha b hb
    simp_all
  have : {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d} = (∅ : Set ℕ) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    simp [this]
  simp [this]

@[simp]
theorem dist_le_card (C : Set (n → R)) : dist C ≤ Fintype.card n := by
  by_cases h : Subsingleton C
  · simp
  · simp at h
    unfold Set.Nontrivial at h
    obtain ⟨u, hu, v, hv, huv⟩ := h
    refine Nat.sInf_le ?_
    simp
    refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, hammingDist_le_card_fintype⟩⟩⟩

/-- If `u` and `v` are two codewords of `C` with distance less than `dist C`,
then they are the same. -/
theorem eq_of_lt_dist {C : Set (n → R)} {u v : n → R} (hu : u ∈ C) (hv : v ∈ C)
    (huv : Δ₀(u, v) < ‖C‖₀) : u = v := by
  simp only [dist] at huv
  by_contra hNe
  push_neg at hNe
  revert huv
  simp
  refine Nat.sInf_le ?_
  simp only [Set.mem_setOf_eq]
  refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨hNe, le_rfl⟩⟩⟩

@[simp]
theorem distFromCode_of_empty (u : n → R) : Δ₀(u, (∅ : Set (n → R))) = ⊤ := by
  simp [distFromCode]

theorem distFromCode_eq_top_iff_empty (u : n → R) (C : Set (n → R)) : Δ₀(u, C) = ⊤ ↔ C = ∅ := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    apply sInf_eq_top.mp at h
    revert h
    simp
    refine ⟨Fintype.card n, v, And.intro hv ⟨?_, ?_⟩⟩
    · norm_num; exact hammingDist_le_card_fintype
    · norm_num
  · intro h; subst h; simp

@[simp]
theorem distFromCode_of_mem (C : Set (n → R)) {u : n → R} (h : u ∈ C) : Δ₀(u, C) = 0 := by
  simp only [distFromCode]
  apply ENat.sInf_eq_zero.mpr
  simp [h]

theorem distFromCode_eq_zero_iff_mem (C : Set (n → R)) (u : n → R) : Δ₀(u, C) = 0 ↔ u ∈ C := by
  apply Iff.intro
  · simp only [distFromCode]
    intro h
    apply ENat.sInf_eq_zero.mp at h
    revert h
    simp
  · intro h; exact distFromCode_of_mem C h

theorem distFromCode_eq_of_lt_half_dist (C : Set (n → R)) (u : n → R) {v w : n → R}
    (hv : v ∈ C) (hw : w ∈ C) (huv : Δ₀(u, v) < ‖C‖₀ / 2) (hvw : Δ₀(u, w) < ‖C‖₀ / 2) : v = w := by
  apply eq_of_lt_dist hv hw
  calc
    Δ₀(v, w) ≤ Δ₀(v, u) + Δ₀(u, w) := by exact hammingDist_triangle v u w
    _ = Δ₀(u, v) + Δ₀(u, w) := by simp only [hammingDist_comm]
    _ < ‖C‖₀ / 2 + ‖C‖₀ / 2 := by omega
    _ ≤ ‖C‖₀ := by omega

section Computable

/-- Computable version of the Hamming distance of a code `C`, assuming `C` is a `Fintype`.

The return type is `ℕ∞` since we use `Finset.min`. -/
def dist' (C : Set (n → R)) [Fintype C] : ℕ∞ :=
  Finset.min <| ((@Finset.univ (C × C) _).filter (fun p => p.1 ≠ p.2)).image
    (fun ⟨u, v⟩ => hammingDist u.1 v.1)

notation "‖" C "‖₀'" => dist' C

variable {C : Set (n → R)} [Fintype C]

@[simp]
theorem dist'_empty : ‖(∅ : Set (n → R))‖₀' = ⊤ := by
  simp [dist']

@[simp]
theorem codeDist'_subsingleton [Subsingleton C] : ‖C‖₀' = ⊤ := by
  simp [dist']
  apply Finset.min_eq_top.mpr
  simp [Finset.filter_eq_empty_iff]
  have h := @Subsingleton.elim C _
  simp_all
  exact h

theorem dist'_eq_dist : ‖C‖₀'.toNat = ‖C‖₀ := by
  by_cases h : Subsingleton C
  · simp
  · simp [dist, dist']
    have : dist' C ≠ ⊤ := by sorry
    sorry
    -- apply (ENat.toNat_eq_iff this).mp
    -- apply Finset.min_eq_top.mp
    -- simp [this]

section

/-
- TODO: We currently do not use `(E)Dist` as it forces the distance(s) into `ℝ`.
        Instead, we take some explicit notion of distance `δf`.
        Let us give this some thought.
-/

variable {α : Type*}
         {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- The set of possible distances `δf` from a vector `w` to a code `C`.
-/
def possibleDistsToCode (w : ι → F) (C : Set (ι → F)) (δf : (ι → F) → (ι → F) → α) : Set α :=
  {d : α | ∃ c ∈ C, c ≠ w ∧ δf w c = d}

/-- The set of possible distances `δf` between distinct codewords in a code `C`.

  - TODO: This allows us to express distance in non-ℝ, which is quite convenient.
          Extending to `(E)Dist` forces this into `ℝ`; give some thought.
-/
def possibleDists (C : Set (ι → F)) (δf : (ι → F) → (ι → F) → α) : Set α :=
  {d : α | ∃ p ∈ Set.offDiag C, δf p.1 p.2 = d}

/-- A generalisation of `distFromCode` for an arbitrary distance function `δf`.
-/
noncomputable def distToCode [LinearOrder α] [Zero α]
                             (w : ι → F) (C : Set (ι → F))
                             (δf : (ι → F) → (ι → F) → α)
                             (h : (possibleDistsToCode w C δf).Finite) : WithTop α :=
  haveI := @Fintype.ofFinite _ h
  (possibleDistsToCode w C δf).toFinset.min

end

lemma distToCode_of_nonempty {α : Type*} [LinearOrder α] [Zero α]
                             {ι F : Type*}
                             {w : ι → F} {C : Set (ι → F)}
                             {δf : (ι → F) → (ι → F) → α}
                             (h₁ : (possibleDistsToCode w C δf).Finite)
                             (h₂ : (possibleDistsToCode w C δf).Nonempty) :
  haveI := @Fintype.ofFinite _ h₁
  distToCode w C δf h₁ = .some ((possibleDistsToCode w C δf).toFinset.min' (by simpa)) := by
  simp [distToCode, Finset.min'_eq_inf', Finset.min_eq_inf_withTop]
  rfl

/-- Computable version of the distance from a vector `u` to a code `C`, assuming `C` is a `Fintype`.
-/
def distFromCode' (C : Set (n → R)) [Fintype C] (u : n → R) : ℕ∞ :=
Finset.min <| (@Finset.univ C _).image (fun v => hammingDist u v.1)

notation "Δ₀'(" u ", " C ")" => distFromCode' C u

end Computable

noncomputable section

variable {ι : Type*} [Fintype ι]
         {F : Type*}
         {u v w c : ι → F}
         {C : Set (ι → F)}

section

variable [Nonempty ι] [DecidableEq F]

def relHammingDist (u v : ι → F) : ℚ≥0 :=
  hammingDist u v / Fintype.card ι

/--
  `δᵣ(u,v)` denotes the relative Hamming distance between vectors `u` and `v`.
-/
notation "δᵣ(" u ", " v ")" => relHammingDist u v

/-- The relative Hamming distance between two vectors is at most `1`.
-/
@[simp]
lemma relHammingDist_le_one : δᵣ(u, v) ≤ 1 := by
  unfold relHammingDist
  qify
  rw [div_le_iff₀ (by simp)]
  simp [hammingDist_le_card_fintype]

/-- The relative Hamming distance between two vectors is non-negative.
-/
@[simp]
lemma zero_le_relHammingDist : 0 ≤ δᵣ(u, v) := by
  unfold relHammingDist
  qify
  rw [le_div_iff₀ (by simp)]
  simp

end

/-- The range of the relative Hamming distance function.
-/
def relHammingDistRange (ι : Type*) [Fintype ι] : Set ℚ≥0 :=
  {d : ℚ≥0 | ∃ d' : ℕ, d' ≤ Fintype.card ι ∧ d = d' / Fintype.card ι}

/-- The range of the relative Hamming distance is well-defined.
-/
@[simp]
lemma relHammingDist_mem_relHammingDistRange [DecidableEq F] : δᵣ(u, v) ∈ relHammingDistRange ι :=
  ⟨hammingDist _ _, Finset.card_filter_le _ _, rfl⟩

/-- The range of the relative Hamming distance function is finite.
-/
@[simp]
lemma finite_relHammingDistRange [Nonempty ι] : (relHammingDistRange ι).Finite := by
  simp only [relHammingDistRange, ← Set.finite_coe_iff, Set.coe_setOf]
  exact
    finite_iff_exists_equiv_fin.2
      ⟨Fintype.card ι + 1,
        ⟨⟨
        fun ⟨s, _⟩ ↦ ⟨(s * Fintype.card ι).num, by aesop (add safe (by omega))⟩,
        fun n ↦ ⟨n / Fintype.card ι, by use n; simp [Nat.le_of_lt_add_one n.2]⟩,
        fun ⟨_, _, _, h₂⟩ ↦ by field_simp [h₂],
        fun _ ↦ by simp
        ⟩⟩
      ⟩

/-- The set of pairs of distinct elements from a finite set is finite.
-/
@[simp]
lemma finite_offDiag [Finite F] : C.offDiag.Finite := Set.Finite.offDiag (Set.toFinite _)

section

variable [DecidableEq F]

/-- The set of possible distances between distinct codewords in a code.
-/
def possibleRelHammingDists (C : Set (ι → F)) : Set ℚ≥0 :=
  possibleDists C relHammingDist

/-- The set of possible distances between distinct codewords in a code is a subset of the range of
  the relative Hamming distance function.
-/
@[simp]
lemma possibleRelHammingDists_subset_relHammingDistRange :
  possibleRelHammingDists C ⊆ relHammingDistRange ι := fun _ ↦ by
    aesop (add simp [possibleRelHammingDists, possibleDists])

variable [Nonempty ι]

/-- The set of possible distances between distinct codewords in a code is a finite set.
-/
@[simp]
lemma finite_possibleRelHammingDists : (possibleRelHammingDists C).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleRelHammingDists_subset_relHammingDistRange

open Classical in
/-- The minimum relative Hamming distance of a code.
-/
def minRelHammingDistCode (C : Set (ι → F)) : ℚ≥0 :=
  haveI : Fintype (possibleRelHammingDists C) := @Fintype.ofFinite _ finite_possibleRelHammingDists
  if h : (possibleRelHammingDists C).Nonempty
  then (possibleRelHammingDists C).toFinset.min' (Set.toFinset_nonempty.2 h)
  else 0

end

/--
  `δᵣ C` denotes the minimum relative Hamming distance of a code `C`.
-/
notation "δᵣ" C => minRelHammingDistCode C

/-- The range set of possible relative Hamming distances from a vector to a code is a subset
  of the range of the relative Hamming distance function.
-/
@[simp]
lemma possibleRelHammingDistsToC_subset_relHammingDistRange [DecidableEq F] :
  possibleDistsToCode w C relHammingDist ⊆ relHammingDistRange ι := fun _ ↦ by
    aesop (add simp Code.possibleDistsToCode)

/-- The set of possible relative Hamming distances from a vector to a code is a finite set.
-/
@[simp]
lemma finite_possibleRelHammingDistsToCode [Nonempty ι] [DecidableEq F] :
  (possibleDistsToCode w C relHammingDist).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleRelHammingDistsToC_subset_relHammingDistRange

instance [Nonempty ι] [DecidableEq F] : Fintype (possibleDistsToCode w C relHammingDist)
  := @Fintype.ofFinite _ finite_possibleRelHammingDistsToCode

open Classical in
/-- The relative Hamming distance from a vector to a code.
-/
def relHammingDistToCode [Nonempty ι] [DecidableEq F] (w : ι → F) (C : Set (ι → F)) : ℚ≥0 :=
  if h : (possibleDistsToCode w C relHammingDist).Nonempty
  then distToCode w C relHammingDist finite_possibleRelHammingDistsToCode |>.get (p h)
  else 0
  where p (h : (possibleDistsToCode w C relHammingDist).Nonempty) := by
          by_contra c
          simp [distToCode] at c ⊢
          rw [WithTop.none_eq_top, Finset.min_eq_top, Set.toFinset_eq_empty] at c
          simp_all

/--
  `δᵣ(w,C)` denotes the relative Hamming distance between a vector `w` and a code `C`.
-/
notation "δᵣ(" w ", " C ")" => relHammingDistToCode w C

@[simp]
lemma zero_mem_relHammingDistRange : 0 ∈ relHammingDistRange ι := by use 0; simp

/-- The relative Hamming distances between a vector and a codeword is in the
  range of the relative Hamming distance function.
-/
@[simp]
lemma relHammingDistToCode_mem_relHammingDistRange [Nonempty ι] [DecidableEq F] :
  δᵣ(c, C) ∈ relHammingDistRange ι := by
  unfold relHammingDistToCode
  split_ifs with h
  · exact Set.mem_of_subset_of_mem
            (s₁ := (possibleDistsToCode c C relHammingDist).toFinset)
            (by simp)
            (by simp_rw [distToCode_of_nonempty (h₁ := by simp) (h₂ := h)]
                simp [←WithTop.some_eq_coe]
                have := Finset.min'_mem
                          (s := (possibleDistsToCode c C relHammingDist).toFinset)
                          (H := by simpa)
                simpa)
  · simp

end

noncomputable section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]


open Finset

def wt [Zero F]
  (v : ι → F) : ℕ := #{i | v i ≠ 0}

lemma wt_eq_hammingNorm [Zero F] {v : ι → F} :
  wt v = hammingNorm v := rfl

lemma wt_eq_zero_iff [Zero F] {v : ι → F} :
  wt v = 0 ↔ Fintype.card ι = 0 ∨ ∀ i, v i = 0 := by
  by_cases IsEmpty ι <;>
  aesop (add simp [wt, Finset.filter_eq_empty_iff])

end

end Code

variable [Finite R]

open Fintype

def projection (S : Finset n) (w : n → R) : S → R :=
  fun i => w i.val

omit [Finite R] in theorem projection_injective
    (C : Set (n → R))
    (nontriv : ‖C‖₀ ≥ 1)
    (S : Finset n)
    (hS : card S = card n - (‖C‖₀ - 1))
    (u v : n → R)
    (hu : u ∈ C)
    (hv : v ∈ C) : projection S u = projection S v → u = v := by
  intro proj_agree
  by_contra hne

  have hdiff : hammingDist u v ≥ ‖C‖₀ := by
    simp [Code.dist]
    refine Nat.sInf_le ?_
    refine Set.mem_setOf.mpr ?_
    use u
    refine exists_and_left.mp ?_
    use v

  let D := {i : n | u i ≠ v i}

  have hD : card D = hammingDist u v := by
    simp
    exact rfl

  have hagree : ∀ i ∈ S, u i = v i := by
    intros i hi
    let i' : {x // x ∈ S} := ⟨i, hi⟩
    have close: u i' = v i' := by
      apply congr_fun at proj_agree
      apply proj_agree
    exact close

  have hdisjoint : D ∩ S = ∅ := by
    by_contra hinter
    have hinter' : (D ∩ S).Nonempty := by
      exact Set.nonempty_iff_ne_empty.mpr hinter
    apply Set.inter_nonempty.1 at hinter'
    obtain ⟨x, hx_in_D, hx_in_S⟩ := hinter'
    apply hagree at hx_in_S
    contradiction

  let diff : Set n := {i : n | ¬i ∈ S}

  have hsub : D ⊆ diff  := by
    unfold diff
    refine Set.subset_setOf.mpr ?_
    intro x hxd
    solve_by_elim

  have hcard_compl : @card diff (ofFinite diff) = ‖C‖₀ - 1 := by
    unfold diff
    simp at *
    rw[hS]
    have stronger : ‖C‖₀ ≤ card n := by
      apply Code.dist_le_card
    omega

  have hsizes: card D ≤ @card diff (ofFinite diff) := by
    exact @Set.card_le_card _ _ _ _ (ofFinite diff) hsub

  rw[hcard_compl, hD] at hsizes
  omega

/-- **Singleton bound** for arbitrary codes -/
theorem singleton_bound (C : Set (n → R)) :
    (ofFinite C).card ≤ (ofFinite R).card ^ (card n - (‖C‖₀ - 1)) := by

  by_cases non_triv : ‖C‖₀ ≥ 1
  · -- there exists some projection S of the desired size
    have ax_proj: ∃ (S : Finset n), card S = card n - (‖C‖₀ - 1) := by
      let instexists := Finset.le_card_iff_exists_subset_card
         (α := n)
         (s := @Fintype.elems n _)
         (n := card n - (‖C‖₀ - 1))
      have some: card n - (‖C‖₀ - 1) ≤ card n := by
        omega
      obtain ⟨t, ht⟩ := instexists.1 some
      exists t
      simp
      exact And.right ht
    obtain ⟨S, hS⟩ := ax_proj

    -- project C by only looking at indices in S
    let Cproj := Set.image (projection S) C

    -- The size of C is upper bounded by the size of its projection,
    -- because the projection is injective
    have C_le_Cproj: @card C (ofFinite C) ≤ @card Cproj (ofFinite Cproj) := by
      apply @Fintype.card_le_of_injective C Cproj
        (ofFinite C)
        (ofFinite Cproj)
        (Set.imageFactorization (projection S) C)
      refine Set.imageFactorization_injective_iff.mpr ?_
      intro u hu v hv heq

      apply projection_injective (nontriv := non_triv) (S := S) (u := u) (v := v) <;>
        assumption

    -- The size of Cproj itself is sufficiently bounded by its type
    have Cproj_le_type_card :
    @card Cproj (ofFinite Cproj) ≤ @card R (ofFinite R) ^ (card n - (‖C‖₀ - 1)) := by
      let card_fun := @card_fun S R (Classical.typeDecidableEq S) _ (ofFinite R)
      rw[hS] at card_fun
      rw[← card_fun]

      let huniv := @set_fintype_card_le_univ (S → R) ?_ Cproj (ofFinite Cproj)
      exact huniv

    apply le_trans (b := @card Cproj (ofFinite Cproj)) <;>
      assumption
  · simp at non_triv
    rw[non_triv]
    simp only [zero_tsub, tsub_zero]

    let card_fun := @card_fun n R (Classical.typeDecidableEq n) _ (ofFinite R)
    rw[← card_fun]

    let huniv := @set_fintype_card_le_univ (n → R) ?_ C (ofFinite C)
    exact huniv


abbrev LinearCode.{u, v} (ι : Type u) [Fintype ι] (F : Type v) [Semiring F] : Type (max u v) :=
  Submodule F (ι → F)

namespace LinearCode

section

variable {F : Type*}
         {ι : Type*} [Fintype ι]
         {κ : Type*} [Fintype κ]

/--
Linear code defined by left multiplication by its generator matrix.
-/
noncomputable def fromRowGenMat [Semiring F] (G : Matrix κ ι F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear

/-- Linear code defined by right multiplication by a generator matrix.
-/
noncomputable def fromColGenMat [CommRing F] (G : Matrix ι κ F) : LinearCode ι F :=
  LinearMap.range G.mulVecLin

/-- Define a linear code from its (parity) check matrix -/
noncomputable def byCheckMatrix [CommRing F] (H : Matrix ι κ F) : LinearCode κ F :=
  LinearMap.ker H.mulVecLin

/-- The Hamming distance of a linear code can also be defined as the minimum Hamming norm of a
  non-zero vector in the code -/
noncomputable def disFromHammingNorm [Semiring F] [DecidableEq F] (LC : LinearCode ι F) : ℕ :=
  sInf {d | ∃ u ∈ LC, u ≠ 0 ∧ hammingNorm u ≤ d}

-- Require `[CommRing R]`
theorem dist_eq_dist_from_HammingNorm [Semiring F] [DecidableEq F] (LC : LinearCode ι F) :
    Code.dist LC.carrier = disFromHammingNorm LC := by
  simp [Code.dist, disFromHammingNorm]
  congr; unfold setOf; funext d
  apply Eq.propIntro <;> intro h
  · obtain ⟨u, hu, v, hv, huv, hDist⟩ := h
    -- let w := u - v
    -- have hw : w ∈ C := by simp [Submodule.add_mem]
    -- refine ⟨w, And.intro hw ⟨v, And.intro hv ⟨huv, ?_⟩⟩⟩
    sorry
  · obtain ⟨u, hu, hNorm, hDist⟩ := h
    -- refine ⟨u, And.intro hu ⟨v, And.intro hv ⟨huv, ?_⟩⟩⟩
    sorry

/--
The dimension of a linear code.
-/
noncomputable def dim [Semiring F] (LC : LinearCode ι F) : ℕ :=
  Module.finrank F LC

/-- The dimension of a linear code equals the rank of its associated generator matrix.
-/
lemma rank_eq_dim_fromColGenMat [CommRing F] {G : Matrix κ ι F} :
  G.rank = dim (fromColGenMat G) := rfl

/--
The length of a linear code.
-/
def length [Semiring F] (_ : LinearCode ι F) : ℕ := Fintype.card ι

/--
The rate of a linear code.
-/
noncomputable def rate [Semiring F] (LC : LinearCode ι F) : ℚ≥0 :=
  (dim LC : ℚ≥0) / length LC

/--
  `ρ LC` is the rate of the linear code `LC`.
-/
notation "ρ" LC => rate LC

end

section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- The minimum taken over the weight of codewords in a linear code.
-/
noncomputable def minWtCodewords [Semiring F] (LC : LinearCode ι F) : ℕ :=
  sInf {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w}

/--
The Hamming distance between codewords equals to the weight of their difference.
-/
lemma hammingDist_eq_wt_sub [CommRing F] {u v : ι → F} : hammingDist u v = Code.wt (u - v) := by
  aesop (add simp [hammingDist, Code.wt, sub_eq_zero])

/--
The min distance of a linear code equals the minimum of the weights of non-zero codewords.
-/
lemma dist_eq_minWtCodewords [CommRing F] {LC : LinearCode ι F} :
  Code.minDist (LC : Set (ι → F)) = minWtCodewords LC := by
    unfold Code.minDist minWtCodewords
    refine congrArg _ (Set.ext fun _ ↦ ⟨fun ⟨u, _, v, _⟩ ↦ ⟨u - v, ?p₁⟩, fun _ ↦ ⟨0, ?p₂⟩⟩) <;>
    aesop (add simp [hammingDist_eq_wt_sub, sub_eq_zero])


open Finset in

lemma dist_UB [CommRing F] {LC : LinearCode ι F} :
    Code.minDist (LC : Set (ι → F)) ≤ length LC := by
  rw [dist_eq_minWtCodewords, minWtCodewords]
  exact sInf.sInf_UB_of_le_UB fun s ⟨_, _, _, s_def⟩ ↦
          s_def ▸ le_trans (card_le_card (subset_univ _)) (le_refl _)

theorem singletonBound [Semiring F] (LC : LinearCode ι F) :
  dim LC ≤ length LC - Code.minDist (LC : Set (ι → F)) + 1 := by sorry


/-- The interleaving of a linear code `LC` over index set `ι` is the submodule spanned by
`ι × n`-matrices whose rows are elements of `LC`. -/
def interleaveCode [Semiring F] [DecidableEq F] (C : Submodule F (n → F)) (ι : Type*)
  : Submodule F ((ι × n) → F) :=
  Submodule.span F {v | ∀ i, ∃ c ∈ C, c = fun j => v (i, j)}

notation:20 C "^⋈" ι => interleaveCode C ι

-- instance : Fintype (interleaveCode C ι) := sorry

/-- Interleave two functions `u v : α → β`. -/
def Function.interleave₂ {α β : Type*} (u v : α → β) : (Fin 2) × α → β :=
  Function.uncurry (fun a => if a = 0 then u else v)

notation:20 u "⋈" v => Function.interleave₂ u v

/-- **Singleton bound** for linear codes -/
theorem singleton_bound_linear [Semiring F] (LC : LinearCode ι F) :
    Module.finrank F LC ≤ card n - (Code.dist LC.carrier) + 1 := by sorry
  -- have : (ofFinite C).card = (ofFinite R).card ^ (Module.finrank R C) := by

end

section Computable

/-- A computable version of the Hamming distance of a linear code `LC`. -/
def linearCodeDist' {F} {ι} [Fintype ι] [Semiring F] [DecidableEq F] [Fintype F] [DecidableEq ι]
 (LC : LinearCode ι F) [DecidablePred (· ∈ LC)] : ℕ∞ :=
  Finset.min <| ((Finset.univ (α := LC)).filter (fun v => v ≠ 0)).image (fun v => hammingNorm v.1)

end Computable

end LinearCode

lemma poly_eq_zero_of_dist_lt {n k : ℕ} {F : Type*} [DecidableEq F] [CommRing F] [IsDomain F]
  {p : Polynomial F} {ωs : Fin n → F}
  (h_deg : p.natDegree < k)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_dist : Δ₀(p.eval ∘ ωs, 0) < n - k + 1)
  : p = 0 := by
  by_cases hk : k = 0
  · simp [hk] at h_deg
  · have h_n_k_1 : n - k + 1 = n - (k - 1) := by omega
    rw [h_n_k_1] at h_dist
    simp [hammingDist] at *
    rw [←Finset.compl_filter, Finset.card_compl] at h_dist
    simp at h_dist
    have hk : 1 ≤ k := by omega
    rw [←Finset.card_image_of_injective _ h_inj
    ] at h_dist
    have h_dist_p : k  ≤
      (@Finset.image (Fin n) F _ ωs {i | Polynomial.eval (ωs i) p = 0} : Finset F).card
        := by omega
    by_cases heq_0 : p = 0 <;> try simp [heq_0]
    have h_dist := Nat.le_trans h_dist_p (by {
      apply Polynomial.card_le_degree_of_subset_roots (p := p)
      intro x hx
      aesop
    })
    omega

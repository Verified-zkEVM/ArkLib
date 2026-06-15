/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.Basic.Distance
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import CompPoly.Data.Nat.Bitwise

/-!
# Linear-Code Constructions and Bounds

This module contains weight/projection lemmas, the singleton bound for arbitrary and
linear codes, and basic constructions and dimension/rate facts for linear codes.

## References

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BCGM25]

-/

variable {n : Type*} [Fintype n] {R : Type*} [DecidableEq R]

namespace Code

noncomputable section
section

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

end
end Code

variable [Finite R]

open Fintype

def projection (S : Finset n) (w : n → R) : S → R :=
  fun i => w i.val

omit [Finite R] in
theorem projection_injective
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
    simp only [Code.dist, ne_eq, ge_iff_le]
    refine Nat.sInf_le ?_
    refine Set.mem_setOf.mpr ?_
    use u
    refine exists_and_left.mp ?_
    use v
  let D := {i : n | u i ≠ v i}
  have hD : card D = hammingDist u v := Fintype.card_subtype _
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
    simp only [ge_iff_le, card_coe, Set.coe_setOf, card_subtype_compl] at *
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
      simp only [card_coe]
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
  · simp only [ge_iff_le, not_le, Nat.lt_one_iff] at non_triv
    rw[non_triv]
    simp only [zero_tsub, tsub_zero]
    let card_fun := @card_fun n R (Classical.typeDecidableEq n) _ (ofFinite R)
    rw[← card_fun]
    let huniv := @set_fintype_card_le_univ (n → R) ?_ C (ofFinite C)
    exact huniv

/-- A `ModuleCode ι F A` is an `F`-linear code of length indexed by `ι` over the alphabet `A`,
defined as an `F`-submodule of `ι → A`. -/
@[simp]
abbrev ModuleCode.{u, v, w} (ι : Type u) (F : Type v) [Semiring F] -- ModuleCode ι F A
    (A : Type w) [AddCommMonoid A] [Module F A] : Type (max u w) := Submodule F (ι → A)

abbrev LinearCode.{u, v} (ι : Type u) [Fintype ι] (F : Type v) [Semiring F] : Type (max u v) :=
  Submodule F (ι → F)

lemma LinearCode_is_ModuleCode.{u, v} {ι : Type u} [Fintype ι] {F : Type v} [Semiring F] :
    LinearCode ι F = ModuleCode ι F F := by
  rfl

namespace LinearCode

section

variable {F : Type*} {A : Type*} [AddCommMonoid A]
         {ι : Type*} [Fintype ι]
         {κ : Type*} [Fintype κ]

/-- The Hamming distance of a linear code can also be defined as the minimum Hamming norm of a
  non-zero vector in the code -/
noncomputable def disFromHammingNorm [Semiring F] [DecidableEq F] (LC : LinearCode ι F) : ℕ :=
  sInf {d | ∃ u ∈ LC, u ≠ 0 ∧ hammingNorm u ≤ d}

theorem dist_eq_dist_from_HammingNorm [CommRing F] [DecidableEq F] (LC : LinearCode ι F) :
    Code.dist LC.carrier = disFromHammingNorm LC := by
  simp only [Code.dist, Submodule.carrier_eq_coe, SetLike.mem_coe, ne_eq, disFromHammingNorm]
  congr; funext d
  apply propext
  constructor
  · intro h
    rcases h with ⟨u, hu, v, hv, huv, hle⟩
    -- Consider the difference w = u - v ∈ LC, w ≠ 0, and ‖w‖₀ = Δ₀(u,v)
    refine ⟨u - v, ?_, ?_, ?_⟩
    · -- membership
      have : (u - v) ∈ LC := by
        simpa [sub_eq_add_neg] using LC.add_mem hu (LC.neg_mem hv)
      simpa using this
    · -- nonzero
      intro hzero
      have : u = v := sub_eq_zero.mp hzero
      exact huv this
    · -- norm bound via `hammingDist_eq_hammingNorm`
      have hEq : hammingNorm (u - v) = hammingDist u v := by
        simp [hammingDist, hammingNorm, sub_ne_zero]
      simpa [hEq] using hle
  · intro h
    rcases h with ⟨w, hw, hw_ne, hle⟩
    -- Take v = 0, u = w
    refine ⟨w, hw, (0 : ι → F), LC.zero_mem, ?_, ?_⟩
    · exact by simpa using hw_ne
    · -- Δ₀(w, 0) = ‖w‖₀
      have hEq : hammingDist w 0 = hammingNorm w := by
        simp [hammingDist, hammingNorm]
      simpa [hEq] using hle

/--
The dimension of a linear code.
-/
noncomputable def dim [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) : ℕ := Module.finrank F MC

/--
The length of a linear code.
-/
def length [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A]
    (_ : ModuleCode ι F A) : ℕ :=
  Fintype.card ι

/--
The rate of a linear code.
-/
noncomputable def rate [Semiring F] {A : Type*} [AddCommMonoid A] [Module F A]
    (MC : ModuleCode ι F A) : ℚ≥0 :=
  (dim MC : ℚ≥0) / length MC

/--
  `ρ LC` is the rate of the linear code `LC`.

  Uses `&` to make the notation non-reserved, allowing `ρ` to also be used as a variable name.
-/
scoped syntax &"ρ" term : term

scoped macro_rules
  | `(ρ $t:term) => `(LinearCode.rate $t)

/-- Let `c` be a word of length `ι`. For every finite `ι`-subset `T` , we define the projection of a
word `c` to `T` as the word obtained by restricting the indexing set of `c` to `T`.
We denote this by `c|[T]`.
Definition 3.7 [BCGM25]. -/
def projectedWord [Fintype ι] (c : ι → F) (T : Finset ι) : T → F := Set.restrict T c

notation:60 c "|[" T "]" => projectedWord c T

/-- Let `C` be a code of length `ι`. For every finite `ι`-subset `T`, we define the projected code
`C|[T]` as the set of projected codewords `c|[T]`, for `c ∈ C`.
Definition 3.7 [BCGM25]. -/
def projectedCode [Fintype ι] (C : Set (ι → F)) (T : Finset ι) : Set (T → F) :=
  {w | ∃ c ∈ C, w = c|[T]}

notation:60 C "|[" T "]" => projectedCode C T

/-- Let `T` be a finite subset of `ι`. If every word in a collection lies in the projected code
`C|[T]`, then so do all `F`-linear combinations of these. -/
lemma projectedCode_linearCombination [Field F] (LC : LinearCode ι F) (T : Finset ι) {α : Type}
    [Fintype α] (U : α → (ι → F)) (c : α → F)
    (hU : ∀ j, projectedWord (U j) T ∈ projectedCode LC.carrier T) :
    projectedWord (fun k => ∑ j, c j * U j k) T ∈ projectedCode LC.carrier T := by
  obtain ⟨w, hw⟩ : ∃ w ∈ LC, ∀ t ∈ T, w t = ∑ j, c j * U j t := by
    choose w hw using hU
    use ∑ j, c j • w j
    exact ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hw j |>.1),
      fun t ht => by simp [show ∀ j, U j t = w j t from
        fun j => congr_fun (hw j |>.2) ⟨t, ht⟩]⟩
  exact ⟨w, hw.1, funext fun t => by simpa using Eq.symm (hw.2 t t.2)⟩

/-- A linear code is maximum distance separable (MDS) if its parameters meet the singleton bound. -/
def IsMDS {ι : Type} [Fintype ι] [CommRing F] [DecidableEq F] (LC : LinearCode ι F) : Prop :=
  Code.dist LC.carrier = length LC - dim LC + 1

/-- Every linear code over a field `F` is a finitely generated `F`-module. -/
lemma linear_code_is_FG [Field F] (LC : LinearCode ι F) : LC.FG := Submodule.FG.of_finite

/-- Module code defined by left multiplication by its generator matrix.
For a matrix `G : Matrix κ ι F` (over field `F`) and module `A` over `F`, this generates
the `F`-submodule of `(ι → A)` spanned by the rows of `G` acting on `(κ → A)`.
The matrix acts on vectors `v : κ → A` by : `(G • v)(i) = ∑ k, G k i • v k`
where `G k i : F` is the scalar and `v k : A` is the module element.
-/
noncomputable def fromRowGenMat [Semiring F] (G : Matrix κ ι F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear

/-- Linear code defined by right multiplication by a generator matrix. -/
noncomputable def fromColGenMat [CommRing F] (G : Matrix ι κ F) : LinearCode ι F :=
  LinearMap.range G.mulVecLin

/-- Define a linear code from its (parity) check matrix -/
noncomputable def byCheckMatrix [CommRing F] (H : Matrix ι κ F) : LinearCode κ F :=
  LinearMap.ker H.mulVecLin

/-- Given a linear code of length `ι` and dimension `dim` over a field `F`, there exists a
`dim × ι` matrix over `F` which generates the code.
Theorem 2.2.7 [GRS25]. -/
lemma gen_matrix_exists [Field F] (LC : LinearCode ι F) :
    ∃ (G : Matrix (Fin (dim LC)) ι F), LC = fromRowGenMat G := by
  unfold fromRowGenMat
  have LC_basis := Module.finBasis F LC
  let G : Matrix (Fin (Module.finrank F ↥LC)) ι F :=
    fun i => LC_basis i
  use G
  simp only [range_vecMulLinear, G, Matrix.row]
  ext x
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · intros h
    use LC_basis.equivFun ⟨x, h⟩
    have x_to_lin_comb : (⟨x, h⟩ : LC).1 = ∑ i, LC_basis.equivFun ⟨x, h⟩ i • (LC_basis i).1 := by
      rw (occs := .pos [1]) [←Module.Basis.sum_equivFun LC_basis ⟨x, h⟩, @Submodule.coe_sum]
      congr
    simp only [Module.Basis.equivFun_apply] at x_to_lin_comb ⊢
    exact x_to_lin_comb.symm
  · rintro ⟨x, h⟩
    rw [←h]
    apply Submodule.sum_smul_mem LC x
    intros c _
    exact Submodule.coe_mem (LC_basis c)

/-- A matrix whose rows are a basis of a linear code over a field `F`. -/
noncomputable def matrixFromBasis [Field F] (LC : LinearCode ι F) : Matrix (Fin (dim LC)) ι F :=
  fun i => Module.finBasis F LC i

/-- A linear code is equal to the submodule spanned by the rows of the matrix whose rows form a
basis of the code. -/
lemma eq_span_rows [Field F] (LC : LinearCode ι F) :
    LC = Submodule.span F (Set.range LC.matrixFromBasis) := by
  unfold matrixFromBasis
  ext x
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · intros h
    use (Module.finBasis F LC).equivFun ⟨x, h⟩
    have x_to_lin_comb : (⟨x, h⟩ : LC).1 =
      ∑ i, (Module.finBasis F LC).equivFun ⟨x, h⟩ i • ((Module.finBasis F LC) i).1 := by
      rw (occs := .pos [1]) [←Module.Basis.sum_equivFun (Module.finBasis F LC) ⟨x, h⟩,
       @Submodule.coe_sum]
      congr
    simp only [Module.Basis.equivFun_apply] at x_to_lin_comb ⊢
    exact x_to_lin_comb.symm
  · rintro ⟨x, h⟩
    rw [←h]
    apply Submodule.sum_smul_mem LC x
    intros c _
    exact Submodule.coe_mem ((Module.finBasis F LC) c)

/-- A linear code is equal to the code generated by the rows of the matrix constructed
from a basis of the code.
Note: eq_span_rows is good for linear-algebra-style reasoning, whereas
eq_fromRowGenMat_matrixFromBasis is essentially a coding theory language restatement of it. -/
lemma eq_fromRowGenMat_matrixFromBasis [Field F] (LC : LinearCode ι F) :
    LC = fromRowGenMat (matrixFromBasis LC) := by
  unfold fromRowGenMat
  simp only [range_vecMulLinear, Matrix.row]
  exact eq_span_rows LC

/-- The rank of the generator matrix equals the dimension of the linear code. -/
lemma rank_genMatrix_eq_dim [Field F] (LC : LinearCode ι F) :
    dim LC = (matrixFromBasis LC).rank := by
  unfold dim
  have h := Matrix.rank_eq_finrank_span_row (matrixFromBasis LC)
  symm
  erw [h]
  have := congrArg (fun K : Submodule F (ι → F) => Module.finrank F ↥K) (eq_span_rows LC)
  exact this.symm

/-- The dimension of the linear code given by a generator matrix is the rank of the matrix. -/
lemma dim_fromRowGenMat {k n : ℕ} [Field F] {G : Matrix (Fin k) (Fin n) F} :
    dim (fromRowGenMat G) = G.rank := by
  unfold fromRowGenMat;
  convert congr_arg (fun s : Submodule F _ => Module.finrank F s) _;
  rotate_left;
  · exact Submodule.span F (Set.range (fun i => G i));
  · ext; simp [Matrix.vecMulLinear];
    simp +decide [funext_iff, Matrix.vecMul, Submodule.mem_span_range_iff_exists_fun];
    rfl;
  · convert Matrix.rank_eq_finrank_span_row G using 1

/-- Given a linear code of length `ι` and dimension `dim` over a field `F`, we define its `ι × dim`
generator matrix as a matrix whose columns are an `F`-basis of the code. -/
noncomputable def genMatrixCols [Field F] (LC : LinearCode ι F) :
    Matrix ι (Fin (dim LC)) F := (matrixFromBasis LC).transpose

/-- The dimension of a linear code equals the rank of its associated generator matrix.
-/
lemma rank_eq_dim_fromColGenMat [CommRing F] {G : Matrix κ ι F} :
  G.rank = dim (fromColGenMat G) := rfl

end

section

variable {F : Type*} [DecidableEq F]
         {ι : Type*} [Fintype ι]
         {A : Type*} [AddCommMonoid A] [DecidableEq A]

/-- The minimum taken over the weight of codewords in a linear code.
-/
noncomputable def minWtCodewords [Semiring F] [Module F A] (MC : ModuleCode ι F A) : ℕ :=
  sInf {w | ∃ c ∈ MC, c ≠ 0 ∧ Code.wt c = w}

/--
The Hamming distance between codewords equals to the weight of their difference.
-/
lemma hammingDist_eq_wt_sub [AddCommGroup F] {u v : ι → F} : hammingDist u v = Code.wt (u - v) := by
  aesop (add simp [hammingDist, Code.wt, sub_eq_zero])

omit [DecidableEq F] in
/-- The min distance of a linear code equals the minimum of the weights of non-zero codewords.
-/
lemma dist_eq_minWtCodewords [Ring F] {A : Type*} [DecidableEq A] [AddCommGroup A] [Module F A]
    {MC : ModuleCode ι F A} :
  Code.minDist (MC : Set (ι → A)) = minWtCodewords MC := by
    unfold Code.minDist minWtCodewords
    refine congrArg _ (Set.ext fun _ ↦ ⟨fun ⟨u, _, v, _⟩ ↦ ⟨u - v, ?p₁⟩, fun _ ↦ ⟨0, ?p₂⟩⟩) <;>
    rename_i u hu v u_sub_v_weight hvv h_u_mem hv_u_v_rel
    -- aesop (add simp [hammingDist_eq_wt_sub, sub_eq_zero])
    constructor
    · rcases hv_u_v_rel with ⟨h_v_mem, h_u_ne_v, h_dist⟩
      apply Submodule.sub_mem
      · exact h_u_mem
      · exact h_v_mem
    · -- case p₂
      rcases hv_u_v_rel with ⟨h_v_mem, h_u_ne_v, h_dist⟩
      constructor
      · rw [sub_ne_zero]; exact h_u_ne_v
      · -- ⊢ Code.wt (u - v) = hv
        -- We know `Code.wt c = h_u_mem`, so we show `Δ₀(0, c) = Code.wt c`
        rw [← h_dist]
        simp [Code.wt, hammingDist, sub_eq_zero]
    · simp only [SetLike.mem_coe, ne_eq, hammingDist_zero_left]
      rcases hv_u_v_rel with ⟨c, h_c_mem, h_c_ne, h_c_wt⟩
      -- We need to prove the conjunction
      constructor
      · -- 1. Prove `0 ∈ MC`
        let res := Submodule.zero_mem (p := MC)
        exact res
      · -- 2. Prove `∃ v_1 ...`
        refine ⟨c, h_c_mem, ?_, ?_⟩
        · -- Prove `¬0 = c` (which is `0 ≠ c`)
          exact h_c_ne.symm
        · -- Prove `‖c‖₀ = h_u_mem`
          rw [←h_c_wt]
          simp only [hammingNorm, ne_eq, Code.wt]

open Finset in
omit [DecidableEq F] in
lemma dist_UB [Ring F] {A : Type*} [DecidableEq A] [AddCommGroup A] [Module F A]
    {MC : ModuleCode ι F A} : Code.minDist (MC : Set (ι → A)) ≤ length MC := by
  rw [dist_eq_minWtCodewords, minWtCodewords]
  exact sInf.sInf_UB_of_le_UB fun s ⟨_, _, _, s_def⟩ ↦
          s_def ▸ le_trans (card_le_card (subset_univ _)) (le_refl _)

-- Restriction to a finite set of coordinates as a linear map
noncomputable def restrictLinear [Semiring F] [Module F A] (S : Finset ι) :
  (ι → A) →ₗ[F] (S → A) :=
{ toFun := fun f i => f i.1,
  map_add' := by intro f g; ext i; simp,
  map_smul' := by intro a f; ext i; simp }

theorem singletonBound [CommRing F] [StrongRankCondition F]
    (LC : LinearCode ι F) :
  dim LC ≤ length LC - Code.minDist (LC : Set (ι → F)) + 1 := by
  classical
  -- abbreviations
  set d := Code.minDist (LC : Set (ι → F)) with hd
  -- trivial case when d = 0
  by_cases h0 : d = 0
  · -- dim LC ≤ card ι ≤ card ι - 0 + 1
    have h_le_top : Module.finrank F LC ≤ Module.finrank F (ι → F) :=
      (Submodule.finrank_le (R := F) (M := (ι → F)) LC)
    have h_top : Module.finrank F (ι → F) = Fintype.card ι := Module.finrank_pi (R := F)
    have hfin : Module.finrank F LC ≤ Fintype.card ι := by simpa [h_top] using h_le_top
    have hfin' : Module.finrank F LC ≤ Fintype.card ι + 1 := hfin.trans (Nat.le_add_right _ _)
    have : Module.finrank F LC ≤ 1 + (Fintype.card ι - d) := by
      simpa [h0, Nat.sub_zero, Nat.add_comm] using hfin'
    simpa [dim, length, hd, Nat.add_comm] using this
  -- main case: d ≥ 1
  · have hd_pos : 1 ≤ d := by omega
    -- choose a set S of coordinates with |S| = |ι| - (d - 1)
    have h_le : Fintype.card ι - (d - 1) ≤ Fintype.card ι := by
      exact Nat.sub_le _ _
    obtain ⟨S, -, hScard⟩ :=
      (Finset.le_card_iff_exists_subset_card (α := ι) (s := (Finset.univ : Finset ι))
        (n := Fintype.card ι - (d - 1))).1 h_le
    -- restriction linear map to S, restricted to the code LC
    let res : LC →ₗ[F] (S → F) := (restrictLinear (F := F) (ι := ι) S).comp LC.subtype
    -- show ker res = ⊥ via the minimum distance property
    have hker : LinearMap.ker res = ⊥ := by
      classical
      refine LinearMap.ker_eq_bot'.2 ?_
      intro x hx
      -- x : LC, `res x = 0` hence all S-coordinates vanish
      have hxS : ∀ i ∈ S, (x : ι → F) i = 0 := by
        intro i hi
        have := congrArg (fun (f : (S → F)) => f ⟨i, hi⟩) (by simpa using hx)
        -- simp at this
        simpa using this
      -- bound the weight of x by |Sᶜ|
      let A : Finset ι := Finset.univ.filter (fun i => (x : ι → F) i ≠ 0)
      have hA_subset_compl : A ⊆ Sᶜ := by
        intro i hi
        rcases Finset.mem_filter.mp hi with ⟨-, hne⟩
        have : i ∉ S := by
          intro hiS; have := hxS i hiS; exact hne (by simpa using this)
        simpa [Finset.mem_compl] using this
      have h_wt_le : Code.wt (x : ι → F) ≤ (Sᶜ).card := by
        have : Code.wt (x : ι → F) = A.card := by
          simp [Code.wt, A]
        simpa [this] using (Finset.card_le_card hA_subset_compl)
      -- and |Sᶜ| = d - 1 using the chosen size of S
      have hS_card : S.card = Fintype.card ι - (d - 1) := by simpa using hScard
      have h_wt_le' : Code.wt (x : ι → F) ≤ d - 1 := by
        -- (Sᶜ).card = card ι - S.card = d - 1
        have hcardcompl : (Sᶜ : Finset ι).card = Fintype.card ι - S.card := by
          simpa using (Finset.card_compl (s := S))
        -- compute |Sᶜ| from hS_card
        have h_d_le_len : d ≤ Fintype.card ι := by
          have h := (dist_UB (MC := LC)); simpa [hd, length] using h
        have h_d1_le_len : d - 1 ≤ Fintype.card ι :=
          le_trans (Nat.sub_le d 1) h_d_le_len
        have hlen_sub : Fintype.card ι - S.card = d - 1 := by
          have : Fintype.card ι - S.card = Fintype.card ι - (Fintype.card ι - (d - 1)) := by
            simp [hS_card]
          simpa [Nat.sub_sub_self h_d1_le_len] using this
        have hcompl_le : (Sᶜ : Finset ι).card ≤ d - 1 := by simp [hcardcompl, hlen_sub]
        exact h_wt_le.trans hcompl_le
      -- if x ≠ 0 then d ≤ wt x, contradiction
      have hx0 : (x : ι → F) = 0 := by
        by_contra hx0
        have hx_mem : Code.wt (x : ι → F) ∈ {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w} := by
          exact ⟨x, x.property, by simpa using hx0, rfl⟩
        have hmin_le : d ≤ Code.wt (x : ι → F) := by
          -- d = sInf of weights of nonzero codewords
          have hmin_eq : Code.minDist (LC : Set (ι → F)) = minWtCodewords LC :=
            dist_eq_minWtCodewords (MC := LC)
          have hsInf : sInf {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w} ≤ Code.wt (x : ι → F) :=
            Nat.sInf_le (s := {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w}) hx_mem
          have hd_def : d = sInf {w | ∃ c ∈ LC, c ≠ 0 ∧ Code.wt c = w} := by
            simp [hd, minWtCodewords, hmin_eq]
          simpa [hd_def] using hsInf
        have hcontra : d ≤ d - 1 := le_trans hmin_le h_wt_le'
        have hsucc_le : d + 1 ≤ d := by
          have := Nat.add_le_add_right hcontra 1
          simp [Nat.sub_add_cancel hd_pos, Nat.add_comm] at this
        exact (Nat.not_succ_le_self d) hsucc_le
      -- conclude x = 0 in LC
      apply Subtype.ext
      simpa using hx0
    -- Using injectivity, compare finranks
    have hinj : Function.Injective res := by
      simpa [LinearMap.ker_eq_bot] using hker
    have hrange : Module.finrank F (LinearMap.range res) = Module.finrank F LC :=
      LinearMap.finrank_range_of_inj hinj
    have hcod_le : Module.finrank F (LinearMap.range res) ≤ Module.finrank F (S → F) :=
      Submodule.finrank_le (LinearMap.range res)
    have hcod : Module.finrank F (S → F) = S.card := by
      simp [Module.finrank_pi (R := F) (ι := {x // x ∈ S})]
    have : Module.finrank F LC ≤ S.card := by
      simpa [hrange, hcod] using hcod_le
    -- turn S.card bound into the target bound via arithmetic: a - (d - 1) ≤ 1 + (a - d)
    have hS_to_target : S.card ≤ 1 + (Fintype.card ι - d) := by
      simpa [hScard] using (by omega : Fintype.card ι - (d - 1) ≤ 1 + (Fintype.card ι - d))
    have hfin : Module.finrank F LC ≤ 1 + (Fintype.card ι - d) := this.trans hS_to_target
    simpa [dim, length, hd, Nat.add_comm] using hfin

/-- **Singleton bound** for linear codes -/
theorem singleton_bound_linear [CommRing F] [StrongRankCondition F]
    (LC : LinearCode ι F) :
    Module.finrank F LC ≤ card ι - (Code.dist LC.carrier) + 1 := by
  classical
  -- From the min-distance version and `Code.dist ≤ Code.minDist`.
  have h1 : Module.finrank F LC ≤ card ι - Code.minDist (LC : Set (ι → F)) + 1 :=
    singletonBound (LC := LC)
  -- `dist ≤ minDist` since `= d` implies `≤ d` for witnesses
  have hdist_le_min : Code.dist LC.carrier ≤ Code.minDist (LC : Set (ι → F)) := by
    classical
    let S₁ : Set ℕ := {d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v ≤ d}
    let S₂ : Set ℕ := {d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v = d}
    have hsub : S₂ ⊆ S₁ := by
      intro d hd; rcases hd with ⟨u, hu, v, hv, hne, heq⟩; exact ⟨u, hu, v, hv, hne, by simp [heq]⟩
    by_cases hne : (S₂ : Set ℕ).Nonempty
    · have hLB : ∀ m ∈ S₂, sInf S₁ ≤ m := fun m hm => Nat.sInf_le (s := S₁) (hsub hm)
      have := sInf.le_sInf_of_LB (S := S₂) hne hLB
      simpa [Code.dist, Code.minDist, S₁, S₂] using this
    · -- S₂ empty ⇒ S₁ empty as well
      have hS₂empty : S₂ = (∅ : Set ℕ) := (Set.not_nonempty_iff_eq_empty).1 (by simpa using hne)
      have hS₁empty : S₁ = (∅ : Set ℕ) := by
        apply (Set.eq_empty_iff_forall_notMem).2
        intro m hm
        rcases hm with ⟨u, hu, v, hv, hne, hle⟩
        have : hammingDist u v ∈ S₂ := ⟨u, hu, v, hv, hne, rfl⟩
        simpa [hS₂empty, this]
      simp [Code.dist, Code.minDist, S₁, S₂, hS₁empty, hS₂empty, Nat.sInf_empty]
  -- Since a - b is antitone in b, add 1 afterwards
  have hmono' : card ι - Code.minDist (LC : Set (ι → F)) + 1 ≤
                 card ι - (Code.dist LC.carrier) + 1 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.add_le_add_right (Nat.sub_le_sub_left hdist_le_min _) 1)
  exact h1.trans hmono'

end

section Computable

/-- A computable version of the Hamming distance of a module code `MC`. -/
def moduleCodeDist' {F A} {ι} [Fintype ι] [Semiring F] [Fintype A] [DecidableEq ι] [DecidableEq A]
    [AddCommMonoid A] [Module F A]
 (MC : ModuleCode ι F A) [DecidablePred (· ∈ MC)] : ℕ∞ :=
  Finset.min <| ((Finset.univ (α := MC)).filter (fun v => v ≠ 0)).image (fun v => hammingNorm v.1)

end Computable

end LinearCode

lemma poly_eq_zero_of_dist_lt {n k : ℕ} {F : Type*} [DecidableEq F] [CommRing F] [IsDomain F]
    {p : Polynomial F} {ωs : Fin n → F}
  (h_deg : p.natDegree < k)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_dist : Δ₀(p.eval ∘ ωs, 0) < n - k + 1) : p = 0 := by
  by_cases hk : k = 0
  · simp [hk] at h_deg
  · have h_n_k_1 : n - k + 1 = n - (k - 1) := by omega
    rw [h_n_k_1] at h_dist
    simp only [hammingDist, Function.comp_apply, Pi.zero_apply, ne_eq] at *
    rw [←Finset.compl_filter, Finset.card_compl] at h_dist
    simp only [card_fin] at h_dist
    have hk : 1 ≤ k := by omega
    rw [←Finset.card_image_of_injective _ h_inj
    ] at h_dist
    have h_dist_p : k  ≤
      (@Finset.image (Fin n) F _ ωs {i | Polynomial.eval (ωs i) p = 0} : Finset F).card := by omega
    by_cases heq_0 : p = 0 <;> try simp [heq_0]
    have h_dist := Nat.le_trans h_dist_p (by {
      apply Polynomial.card_le_degree_of_subset_roots (p := p)
      intro x hx
      aesop
    })
    omega

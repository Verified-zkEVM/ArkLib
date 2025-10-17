/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov,
Mirco Richter
-/

import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.Polynomial.Interface
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Henselian

/-!
  # Reed-Solomon Codes

  TODO: define the Reed-Solomon code, and prove its properties.

  TODO: define the Berkelamp-Welch algorithm for unique decoding, and Guruswami-Sudan algorithm for
  list-decoding.
-/

namespace ReedSolomon

open Polynomial NNReal

variable {F : Type*} {ι : Type*} (domain : ι ↪ F)

/-- The evaluation of a polynomial at a set of points specified by `domain : ι ↪ F`, as a linear
  map. -/
def evalOnPoints [Semiring F] : F[X] →ₗ[F] (ι → F) where
  toFun := fun p => fun x => p.eval (domain x)
  map_add' := fun x y => by simp; congr
  map_smul' := fun m x => by simp; congr

/-- The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `domain`.
-/
def code (deg : ℕ) [Semiring F]: Submodule F (ι → F) :=
  (Polynomial.degreeLT F deg).map (evalOnPoints domain)

noncomputable def codewordToPoly
  [Fintype ι] [Field F] [DecidableEq ι]
  {deg : ℕ} {domain : ι ↪ F} (f : code domain deg) : F[X] :=
  Lagrange.interpolate Finset.univ domain.toFun f

variable [Semiring F]

/-- The generator matrix of the Reed-Solomon code of degree `deg` and evaluation points `domain`. -/
def genMatrix (deg : ℕ) : Matrix (Fin deg) ι F :=
  .of fun i j => domain j ^ (i : ℕ)

/-- The (parity)-check matrix of the Reed-Solomon code, assuming `ι` is finite. -/
def checkMatrix (deg : ℕ) [Fintype ι] : Matrix (Fin (Fintype.card ι - deg)) ι F :=
  sorry

-- theorem code_by_genMatrix (deg : ℕ) :
--     code deg = codeByGenMatrix (genMatrix deg) := by
--   simp [codeByGenMatrix, code]
--   rw [LinearMap.range_eq_map]
--   sorry
end ReedSolomon

open Polynomial Matrix Code LinearCode

variable {F ι ι' : Type*}
         {C : Set (ι → F)}

noncomputable section

namespace Vandermonde

/--
A non-square Vandermonde matrix.
-/
def nonsquare [Semiring F] (ι' : ℕ) (α : ι → F) : Matrix ι (Fin ι') F :=
  Matrix.of fun i j => (α i) ^ j.1

lemma nonsquare_mulVecLin [CommSemiring F] {ι' : ℕ} {α₁ : ι ↪ F} {α₂ : Fin ι' → F} {i : ι} :
  (nonsquare ι' α₁).mulVecLin α₂ i = ∑ x, α₂ x * α₁ i ^ x.1 := by
  simp [nonsquare, mulVecLin_apply, mulVec_eq_sum]

/-- The transpose of a non-square Vandermonde matrix.
-/
def nonsquareTranspose [Field F] (ι' : ℕ) (α : ι ↪ F) : Matrix (Fin ι') ι F :=
  (Vandermonde.nonsquare ι' α)ᵀ

section

variable [CommRing F] {m n : ℕ} {α : Fin m → F}

/-- The maximal upper square submatrix of a Vandermonde matrix is a Vandermonde matrix.
-/
lemma subUpFull_of_vandermonde_is_vandermonde (h : n ≤ m) :
  Matrix.vandermonde (α ∘ Fin.castLE h) =
  Matrix.subUpFull (nonsquare n α) (Fin.castLE h) := by
  ext r c
  simp [Matrix.vandermonde, Matrix.subUpFull, nonsquare]

/-- The maximal left square submatrix of a Vandermonde matrix is a Vandermonde matrix.
-/
lemma subLeftFull_of_vandermonde_is_vandermonde (h : m ≤ n) :
  Matrix.vandermonde α = Matrix.subLeftFull (nonsquare n α) (Fin.castLE h) := by
  ext r c
  simp [Matrix.vandermonde, Matrix.subLeftFull, nonsquare]

section

variable [IsDomain F]

/-- The rank of a non-square Vandermonde matrix with more rows than columns is the number of
  columns.
-/
lemma rank_nonsquare_eq_deg_of_deg_le (inj : Function.Injective α) (h : n ≤ m) :
  (Vandermonde.nonsquare (ι' := n) α).rank = n := by
  suffices ((Vandermonde.nonsquare (ι' := n) α).subUpFull (Fin.castLE h)).rank = n by
    exact Matrix.rank_eq_if_subUpFull_eq h this
  rw[
    ←subUpFull_of_vandermonde_is_vandermonde,
    Matrix.rank_eq_if_det_ne_zero
  ]
  rw [@Matrix.det_vandermonde_ne_zero_iff F _ n _ (α ∘ Fin.castLE h)]
  apply Function.Injective.comp <;> aesop (add simp Fin.castLE_injective)

/-- The rank of a non-square Vandermonde matrix with more columns than rows is the number of rows.
-/
lemma rank_nonsquare_eq_deg_of_ι_le (inj : Function.Injective α) (h : m ≤ n) :
  (Vandermonde.nonsquare (ι' := n) α).rank = m := by
  suffices ((Vandermonde.nonsquare (ι' := n) α).subLeftFull (Fin.castLE h)).rank = m by
    exact Matrix.full_row_rank_via_rank_subLeftFull h this
  rw[
    ←subLeftFull_of_vandermonde_is_vandermonde,
    Matrix.rank_eq_if_det_ne_zero]
  rw[Matrix.det_vandermonde_ne_zero_iff]
  exact inj

@[simp]
lemma rank_nonsquare_rows_eq_min (inj : Function.Injective α) :
  (Vandermonde.nonsquare (ι' := n) α).rank = min m n := by
  by_cases h : m ≤ n
  · rw [rank_nonsquare_eq_deg_of_ι_le inj h]; simp [h]
  · rw [rank_nonsquare_eq_deg_of_deg_le inj] <;> omega

end

theorem mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
  {n : ℕ} [NeZero n] {v : ι ↪ F} {p : F[X]} (h_deg : p.natDegree < n) :
  (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) =
  fun i => p.eval (v i) := by
  ext i
  have hLHS :
      (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) i
        = ∑ x ∈ Finset.range n, (if x < n then p.coeff x * v i ^ x else 0) := by
    simp [nonsquare_mulVecLin, Finset.sum_fin_eq_sum_range, Fin.liftF'_p_coeff]
  have hRHS :
      p.eval (v i) = ∑ x ∈ Finset.range n, p.coeff x * v i ^ x :=
    Polynomial.eval_eq_sum_range' (p := p) (x := v i) (n := n) h_deg
  calc
    (Vandermonde.nonsquare (ι' := n) v).mulVecLin (Fin.liftF' p.coeff) i
        = ∑ x ∈ Finset.range n, (if x < n then p.coeff x * v i ^ x else 0) := hLHS
    _ = ∑ x ∈ Finset.range n, p.coeff x * v i ^ x := by
          refine Finset.sum_congr rfl (fun x hx => ?_)
          simp [Finset.mem_range.mp hx]
    _ = p.eval (v i) := by simp [hRHS]

end

end Vandermonde

namespace ReedSolomonCode

section

open Finset Function

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [Field F] [Fintype F]

abbrev RScodeSet (domain : ι ↪ F) (deg : ℕ) : Set (ι → F) := (ReedSolomon.code domain deg).carrier

open Classical in
def toFinset (domain : ι ↪ F) (deg : ℕ) : Finset (ι → F) :=
  (RScodeSet domain deg).toFinset

end

section

variable {deg m n : ℕ} {α : Fin m → F}

section

variable [Semiring F] {p : F[X]}

lemma natDegree_lt_of_mem_degreeLT [NeZero deg] (h : p ∈ degreeLT F deg) : p.natDegree < deg := by
  by_cases p = 0
  · cases deg <;> aesop
  · aesop (add simp [natDegree_lt_iff_degree_lt, mem_degreeLT])

def encode [DecidableEq F] (msg : Fin deg → F) (domain : Fin m ↪ F) : Fin m → F :=
  (polynomialOfCoeffs msg).eval ∘ ⇑domain

lemma encode_mem_ReedSolomon_code [DecidableEq F] [NeZero deg]
    {msg : Fin deg → F} {domain : Fin m ↪ F} :
  encode msg domain ∈ ReedSolomon.code domain deg :=
  ⟨polynomialOfCoeffs msg, ⟨by simp, by ext i; simp [encode, ReedSolomon.evalOnPoints]⟩⟩

end

def makeZero (ι : ℕ) (F : Type*) [Zero F] : Fin ι → F := fun _ ↦ 0

@[simp]
lemma codewordIsZero_makeZero {ι : ℕ} {F : Type*} [Zero F] :
  makeZero ι F = 0 := by unfold makeZero; ext; rfl

open LinearCode

/-- The Vandermonde matrix is the generator matrix for an RS code of length `ι` and dimension `deg`.
-/
lemma genMatIsVandermonde [Fintype ι] [Field F] [DecidableEq F] [inst : NeZero m] {α : ι ↪ F} :
  fromColGenMat (Vandermonde.nonsquare (ι' := m) α) = ReedSolomon.code α m := by
  unfold fromColGenMat ReedSolomon.code
  ext x; rw [LinearMap.mem_range, Submodule.mem_map]
  refine ⟨
    fun ⟨coeffs, h⟩ ↦ ⟨polynomialOfCoeffs coeffs, h.symm ▸ ?p₁⟩,
    fun ⟨p, h⟩ ↦ ⟨Fin.liftF' p.coeff, ?p₂⟩
  ⟩
  · rw [
      ←coeff_polynomialOfCoeffs_eq_coeffs (coeffs := coeffs),
      Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials (by simp)
    ]
    simp [ReedSolomon.evalOnPoints]
  · exact h.2 ▸ Vandermonde.mulVecLin_coeff_vandermondens_eq_eval_matrixOfPolynomials
                  (natDegree_lt_of_mem_degreeLT h.1)

section

open NNReal

variable [Field F]

lemma dim_eq_deg_of_le [NeZero n] (inj : Function.Injective α) (h : n ≤ m) :
  dim (ReedSolomon.code ⟨α, inj⟩ n) = n := by
    classical
    rw [
       ← genMatIsVandermonde, ← rank_eq_dim_fromColGenMat, Vandermonde.rank_nonsquare_rows_eq_min
    ] <;> simp [inj, h]

@[simp]
lemma length_eq_domain_size (inj : Function.Injective α) :
  length (ReedSolomon.code ⟨α, inj⟩ deg) = m := by
  simp [length]

lemma rateOfLinearCode_eq_div [NeZero n] (inj : Function.Injective α) (h : n ≤ m) :
  rate (ReedSolomon.code ⟨α, inj⟩ n) = n / m := by
  rwa [rate, dim_eq_deg_of_le, length_eq_domain_size]

@[simp]
lemma dist_le_length [DecidableEq F] (inj : Function.Injective α) :
    minDist ((ReedSolomon.code ⟨α, inj⟩ n) : Set (Fin m → F)) ≤ m := by
  convert dist_UB
  simp

abbrev sqrtRate [Fintype ι] (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt

end

lemma card_le_card_of_count_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Multiset α} {s' : Multiset β}
  {f : α → β} (inj : Function.Injective f) (h : ∀ a : α, s.count a ≤ s'.count (f a)) :
  s.card ≤ s'.card := by
    classical
    simp only [←Multiset.toFinset_sum_count_eq]
    apply le_trans (b := ∑ x ∈ s.toFinset, s'.count (f x)) (Finset.sum_le_sum (by aesop))
    rw [←Finset.sum_image (f := s'.count) (by aesop (add simp [Set.InjOn]))]
    have : s.toFinset.image f ⊆ s'.toFinset :=
      suffices ∀ x ∈ s, f x ∈ s' by simpa [Finset.image_subset_iff]
      by simp_rw [←Multiset.count_pos]
         exact fun x h' ↦ lt_of_lt_of_le h' (h x)
    exact Finset.sum_le_sum_of_subset_of_nonneg this (by aesop)

section

def constantCode {α : Type*} (x : α) (ι' : Type*) [Fintype ι'] : ι' → α := fun _ ↦ x

variable [Semiring F] {x : F} [Fintype ι] {α : ι ↪ F}

@[simp]
lemma weight_constantCode [DecidableEq F] :
  wt (constantCode x ι) = 0 ↔ IsEmpty ι ∨ x = 0 := by
  by_cases eq : IsEmpty ι <;> aesop (add simp [constantCode, wt_eq_zero_iff])

@[simp]
lemma constantCode_mem_code [NeZero n] :
  constantCode x ι ∈ ReedSolomon.code α n := by
  use C x
  aesop (add simp [ReedSolomon.evalOnPoints, coeff_C, degreeLT])

@[simp]
lemma constantCode_eq_ofNat_zero_iff [Nonempty ι] :
  constantCode x ι = 0 ↔ x = 0 := by
  unfold constantCode
  exact ⟨fun x ↦ Eq.mp (by simp) (congrFun x), (· ▸ rfl)⟩

@[simp]
lemma wt_constantCode [DecidableEq F] [NeZero x] :
  wt (constantCode x ι) = Fintype.card ι := by unfold constantCode wt; aesop

end

open Finset in
/-- The minimal code distance of an RS code of length `ι` and dimension `deg` is `ι - deg + 1`
-/
theorem minDist [Field F] [DecidableEq F] (inj : Function.Injective α) [NeZero n] (h : n ≤ m) :
  minDist ((ReedSolomon.code ⟨α, inj⟩ n) : Set (Fin m → F)) = m - n + 1 := by
  have : NeZero m := by constructor; aesop
  refine le_antisymm ?p₁ ?p₂
  case p₁ =>
    have distUB := singletonBound (LC := ReedSolomon.code ⟨α, inj⟩ n)
    rw [dim_eq_deg_of_le inj h] at distUB
    simp at distUB
    zify [dist_le_length] at distUB
    omega
  case p₂ =>
    rw [dist_eq_minWtCodewords]
    apply le_csInf (by use m, constantCode 1 _; simp)
    intro b ⟨msg, ⟨p, p_deg, p_eval_on_α_eq_msg⟩, msg_neq_0, wt_c_eq_b⟩
    let zeroes : Finset _ := {i | msg i = 0}
    have eq₁ : zeroes.val.Nodup := by
      aesop (add simp [Multiset.nodup_iff_count_eq_one, Multiset.count_filter])
    have msg_zeros_lt_deg : #zeroes < n := by
      apply lt_of_le_of_lt (b := p.roots.card)
                           (hbc := lt_of_le_of_lt (Polynomial.card_roots' _)
                                                  (natDegree_lt_of_mem_degreeLT p_deg))
      exact card_le_card_of_count_inj inj fun i ↦
        if h : msg i = 0
        then suffices 0 < Multiset.count (α i) p.roots by
                rwa [@Multiset.count_eq_one_of_mem (d := eq₁) (h := by simpa [zeroes])]
              by aesop
        else by simp [zeroes, h]
    have : #zeroes + wt msg = m := by
      rw [wt, filter_card_add_filter_neg_card_eq_card]
      simp
    omega

end

end ReedSolomonCode
end

section

open LinearMap Finset

variable {F : Type*} [Field F]
         {ι : Type*} [Fintype ι] [DecidableEq ι]
         {domain : ι ↪ F}
         {deg : ℕ}

/-- The linear map that maps a codeword `f : ι → F` to a degree < |ι| polynomial p,
    such that p(x) = f(x) for all x ∈ ι -/
private noncomputable def interpolate : (ι → F) →ₗ[F] F[X] :=
  Lagrange.interpolate univ domain

/-- The linear map that maps a ReedSolomon codeword to its associated polynomial -/
noncomputable def decode : (ReedSolomon.code domain deg) →ₗ[F] F[X] :=
  domRestrict
    (interpolate (domain := domain))
    (ReedSolomon.code domain deg)

/-- ReedSolomon codewords are decoded into degree < deg polynomials
-/
lemma decoded_polynomial_lt_deg (c : ReedSolomon.code domain deg) :
  decode c ∈ (degreeLT F deg : Submodule F F[X]) := by
  -- Unpack the witness polynomial for this codeword
  rcases c.property with ⟨p, hp_deg, hp_eval⟩
  -- Two cases depending on comparison between `deg` and `|ι|`
  by_cases hle : deg ≤ Fintype.card ι
  · -- In this case, `p` has degree < |ι|, hence uniqueness of interpolation gives `decode c = p`.
    have hp_lt_card : p.degree < (Fintype.card ι : WithBot ℕ) :=
      lt_of_lt_of_le (Polynomial.mem_degreeLT.mp hp_deg) (by exact_mod_cast hle)
    -- Interpolants of equal data are equal
    have hinterp_eq_vals :
      (interpolate (domain := domain)) c =
      Lagrange.interpolate (Finset.univ : Finset ι) domain (fun i => p.eval (domain i)) := by
      refine (Lagrange.interpolate_eq_of_values_eq_on (s := Finset.univ)
                (v := domain) (r := (c : ι → F))
                (r' := fun i => p.eval (domain i))) ?_
      intro i _
      -- From codeword property: evaluations agree on all points
      simpa using congrArg (fun f => f i) hp_eval.symm
    -- A polynomial of degree < |ι| equals its Lagrange interpolant on `univ`
    have hp_eq_interp :
      p = Lagrange.interpolate (Finset.univ : Finset ι) domain (fun i => p.eval (domain i)) :=
        Lagrange.eq_interpolate (s := Finset.univ) (v := domain) (f := p)
          (by intro x _ y _ hxy; exact domain.injective hxy) hp_lt_card
    -- Chain equalities to get `decode c = p`
    have hdecode_eq : decode c = p := by
      -- `hinterp_eq_vals` gives: interpolate _ c = interpolate _ (eval p ∘ domain)
      -- `hp_eq_interp` gives: p = interpolate _ (eval p ∘ domain)
      -- Hence, decode c = p
      have : (interpolate (domain := domain)) c = p :=
        hinterp_eq_vals.trans hp_eq_interp.symm
      simpa [decode, interpolate] using this
    -- Conclude degree bound from membership of `p` in `degreeLT F deg`.
    simpa [hdecode_eq, Polynomial.mem_degreeLT] using hp_deg
  · -- Otherwise, `deg > |ι|`, and interpolation has degree < |ι| ≤ deg
    have hdeg_lt_card : (decode c).degree < (Fintype.card ι : WithBot ℕ) := by
      -- Degree bound for Lagrange interpolation over `univ`
      have := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := domain)
        (r := (c : ι → F)) (by intro x _ y _ hxy; exact domain.injective hxy)
      simpa [decode, interpolate] using this
    have hcard_le_deg : (Fintype.card ι : WithBot ℕ) ≤ deg := by
      have hlt : Fintype.card ι < deg := Nat.lt_of_not_ge hle
      exact le_of_lt (by exact_mod_cast hlt)
    have : (decode c).degree < deg := lt_of_lt_of_le hdeg_lt_card hcard_le_deg
    simpa [Polynomial.mem_degreeLT] using this

/-- The linear map that maps a Reed Solomon codeword to its associated polynomial
    of degree < deg -/
noncomputable def decodeLT : (ReedSolomon.code domain deg) →ₗ[F] (Polynomial.degreeLT F deg) :=
  codRestrict
    (Polynomial.degreeLT F deg)
    decode
    (fun c => decoded_polynomial_lt_deg c)

end

section

open LinearMvExtension

variable {F : Type*} [Semiring F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- A domain `ι ↪ F` is `smooth`, if `ι ⊆ F`, `|ι| = 2^k` for some `k` and
    there exists a subgroup `H` in the group of units `Rˣ`
    and an invertible element `a ∈ R` such that `ι = a • H` -/
class Smooth
  (domain : ι ↪ F) where
    H : Subgroup (Units F)
    a           : Units F
    h_coset     : Finset.image domain Finset.univ
                  = (fun h : Units F => (a : F) * (h : F)) '' (H : Set (Units F))
    h_card_pow2 : ∃ k : ℕ, Fintype.card ι = 2 ^ k

variable {F : Type*} [Field F] [DecidableEq F]
        {ι : Type*} [Fintype ι] [DecidableEq ι]
        {domain : ι ↪ F} [Smooth domain]
        {m : ℕ}

/-- Definition 4.2, WHIR[ACFY24]
  Smooth ReedSolomon Codes are ReedSolomon Codes defined over Smooth Domains, such that
  their decoded univariate polynomials are of degree < 2ᵐ for some m ∈ ℕ. -/
def smoothCode
  (domain : ι ↪ F) [Smooth domain]
  (m : ℕ) : Submodule F (ι → F) := ReedSolomon.code domain (2^m)

/-- The linear map that maps Smooth Reed Solomon Code words
    to their decoded degree wise linear `m`-variate polynomial -/
noncomputable def mVdecode :
  (smoothCode domain m) →ₗ[F] MvPolynomial (Fin m) F :=
    linearMvExtension.comp decodeLT

/-- Auxiliary function to assign values to the weight polynomial variables:
    index `0` ↦ `p.eval b`, index `j+1` ↦ `b j`. -/
private def toWeightAssignment
  (p : MvPolynomial (Fin m) F)
  (b : Fin m → Fin 2) : Fin (m+1) → F :=
    let b' : Fin m → F := fun i => ↑(b i : ℕ)
    Fin.cases (MvPolynomial.eval b' p)
              (fun i => ↑(b i : ℕ))

/-- constraint is true, if ∑ {b ∈ {0,1}^m} w(f(b),b) = σ for given
    m-variate polynomial `f` and `(m+1)`-variate polynomial `w` -/
def weightConstraint
  (f : MvPolynomial (Fin m) F)
  (w : MvPolynomial (Fin (m + 1)) F) (σ : F) : Prop :=
    ∑ b : Fin m → Fin 2 , w.eval (toWeightAssignment f b) = σ

/-- Definition 4.5, WHIR[ACFY24]
  Constrained Reed Solomon codes are smooth codes who's decoded m-variate
  polynomial satisfies the weight constraint for given `w` and `σ`.
-/
def constrainedCode
  (domain : ι ↪ F) [Smooth domain] (m : ℕ)
  (w : MvPolynomial (Fin (m + 1)) F) (σ : F) : Set (ι → F) :=
    { f | ∃ (h : f ∈ smoothCode domain m),
      weightConstraint (mVdecode (⟨f, h⟩ : smoothCode domain m)) w σ }

/-- Definition 4.6, WHIR[ACFY24]
  Multi-constrained Reed Solomon codes are smooth codes who's decoded m-variate
  polynomial satisfies the `t` weight constraints for given `w₀,...,wₜ₋₁` and
    `σ₀,...,σₜ₋₁`.
-/
def multiConstrainedCode
  (domain : ι ↪ F) [Smooth domain] (m t : ℕ)
  (w : Fin t → MvPolynomial (Fin (m + 1)) F)
  (σ : Fin t → F) : Set (ι → F) :=
    { f |
      ∃ (h : f ∈ smoothCode domain m),
        ∀ i : Fin t, weightConstraint (mVdecode (⟨f, h⟩ : smoothCode domain m)) (w i) (σ i)}

end

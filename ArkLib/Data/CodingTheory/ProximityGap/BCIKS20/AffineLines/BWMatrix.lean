/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
public import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.BWMatrix

Definitions and results for this component of ArkLib.
-/

@[expose] public section

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

def BW_homMatrix {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → R) (f : ι → R) :
    Matrix ι (Fin ((e + 1) + (e + k))) R :=
  Matrix.of fun i j =>
    if j.1 < e + 1 then
      f i * (ωs i) ^ j.1
    else
      - (ωs i) ^ (j.1 - (e + 1))

open Polynomial in
theorem BW_homMatrix_entry_natDegree_eq_zero_of_ge {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)) i j).natDegree = 0 := by
  classical
  have hle : ¬ (j.1 ≤ e) := by
    have hgt : e < j.1 := by
      exact lt_of_lt_of_le (Nat.lt_succ_self e) hj
    exact not_le_of_gt hgt
  -- reduce to the second branch
  simp [BW_homMatrix, hle]

open Polynomial in
theorem BW_homMatrix_entry_natDegree_le_one {F : Type} [Field F] {ι : Type} [Fintype ι] (e k : ℕ)
    (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)) i j).natDegree ≤ 1 := by
  by_cases hj : j.1 < e + 1
  · simp only [BW_homMatrix, Matrix.of_apply, hj, ↓reduceIte, ← C_pow]
    refine (natDegree_mul_C_le _ _).trans <| (natDegree_add_le _ _).trans <|
      max_le ((natDegree_C _).trans_le zero_le_one) (natDegree_mul_le.trans ?_)
    rw [natDegree_X, natDegree_C]
  · simp only [BW_homMatrix, Matrix.of_apply, hj, ↓reduceIte, ← C_pow, ← C_neg, natDegree_C]
    exact zero_le_one

open Polynomial in
theorem BW_homMatrix_map_evalRingHom {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs f0 f1 : ι → F) (z : F) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
          (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))).map
        (Polynomial.evalRingHom z)
      =
      BW_homMatrix (ι := ι) e k ωs (fun i => f0 i + z * f1 i) := by
  ext i j
  by_cases hje : (j.1 ≤ e)
  · have hcomm : f1 i * z = z * f1 i := mul_comm (f1 i) z
    have : f1 i * z = z * f1 i ∨ ωs i = 0 ∧ ¬j = 0 := Or.inl hcomm
    simpa [BW_homMatrix, Nat.lt_succ_iff, hje, mul_add, add_mul] using this
  · simp [BW_homMatrix, hje]

open scoped BigOperators in
theorem BW_homMatrix_mulVec_eq_zero_iff {R : Type} [CommRing R] {ι : Type} [Fintype ι] (e k : ℕ)
    (ωs : ι → R) (f : ι → R)
    (a : Fin (e + 1) → R) (b : Fin (e + k) → R) :
    Matrix.mulVec (BW_homMatrix (ι := ι) e k ωs f) (Fin.append a b) = 0 ↔
      (∀ i : ι,
        (∑ t : Fin (e + 1), a t * (ωs i) ^ t.1) * (f i)
          = ∑ s : Fin (e + k), b s * (ωs i) ^ s.1) := by
  classical
  -- helper facts to simplify the `if` guards coming from `BW_homMatrix`
  have hx : ∀ x : Fin (e + 1), (x.1 ≤ e) := fun x => Nat.le_of_lt_succ x.isLt
  have hy : ∀ x : Fin (e + k), ¬ (e + 1 + x.1 ≤ e) := by
    intro x hle
    have : e + 1 ≤ e := le_trans (Nat.le_add_right (e + 1) x.1) hle
    exact Nat.not_succ_le_self e this
  have hrow : ∀ i, Matrix.mulVec (BW_homMatrix (ι := ι) e k ωs f) (Fin.append a b) i =
      (∑ t : Fin (e + 1), a t * ωs i ^ t.1) * f i - ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_add]
    simp only [BW_homMatrix, Order.lt_add_one_iff, Matrix.of_apply, Fin.val_castAdd, hx,
      ↓reduceIte, Fin.append_left, Fin.val_natAdd, hy, add_tsub_cancel_left, Fin.append_right,
      neg_mul, sum_neg_distrib]
    rw [sub_eq_add_neg, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun _ _ ↦ by ring
    · rw [neg_inj]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  constructor
  · intro h i
    exact sub_eq_zero.mp ((hrow i).symm.trans (congrFun h i))
  · intro h
    funext i
    rw [hrow, h i, sub_self, Pi.zero_apply]

open Polynomial in
/-- The determinant of a square polynomial matrix has natural degree at most the sum of
column-wise bounds on the natural degrees of its entries. -/
private theorem natDegree_det_le_sum_of_natDegree_le {R : Type} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R[X]) (d : Fin n → ℕ) (h : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ ↦ ?_
  exact (natDegree_smul_le _ _).trans ((natDegree_prod_le _ _).trans (sum_le_sum fun i _ ↦ h _ _))

open Polynomial in
/-- An entry of the Berlekamp–Welch matrix over `F[X]` has natural degree at most one in the
first `e + 1` columns and zero in the others. -/
private theorem BW_homMatrix_entry_natDegree_le_ite {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs f0 f1 : ι → F) (i : ι) (j : Fin ((e + 1) + (e + k))) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)) i j).natDegree ≤
      if j.1 ≤ e then 1 else 0 := by
  split_ifs with hj
  · exact BW_homMatrix_entry_natDegree_le_one e k ωs f0 f1 i j
  · exact (BW_homMatrix_entry_natDegree_eq_zero_of_ge e k ωs f0 f1 i j (Nat.lt_of_not_ge hj)).le

open scoped BigOperators in
theorem Fin_sum_ite_lt_e_add_one (e k : ℕ) :
    #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e} = e + 1 := by
  rw [Finset.filter_congr fun i _ ↦ Nat.le_iff_lt_add_one, Fin.card_filter_val_lt]
  exact min_eq_right (Nat.le_add_right _ _)

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem BW_homMatrix_det_submatrix_natDegree_le_e_add_one {F : Type} [Field F] {ι : Type}
    [Fintype ι] (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F)
    (r : Fin ((e + 1) + (e + k)) → ι) :
    (Matrix.det
        (Matrix.submatrix
          (BW_homMatrix (ι := ι) e k
            (fun i => (Polynomial.C (ωs i) : F[X]))
            (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)))
          r id)).natDegree ≤ e + 1 := by
  refine (natDegree_det_le_sum_of_natDegree_le _ (fun j ↦ if j.1 ≤ e then 1 else 0)
    fun i j ↦ BW_homMatrix_entry_natDegree_le_ite e k ωs f0 f1 (r i) j).trans_eq ?_
  rw [sum_boole, Nat.cast_id, Fin_sum_ite_lt_e_add_one]


open scoped BigOperators in
open Polynomial in
open Matrix in
theorem BW_homMatrix_det_updateCol_natDegree_le_of_ge {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F)
    (r : Fin ((e + 1) + (e + k)) → ι)
    (i0 : Fin ((e + 1) + (e + k)))
    (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (Matrix.det
        (Matrix.updateCol
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e k
              (fun i => (Polynomial.C (ωs i) : F[X]))
              (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)))
            r id)
          j (Pi.single i0 (1 : F[X])))).natDegree ≤ e + 1 := by
  refine (natDegree_det_le_sum_of_natDegree_le _ (fun x ↦ if x.1 ≤ e then 1 else 0)
    fun i x ↦ ?_).trans_eq ?_
  · rw [Matrix.updateCol_apply]
    by_cases hx : x = j
    · subst hx
      rw [ite_eq_left rfl, ite_eq_right (Nat.not_le_of_gt hj), Pi.single_apply]
      split_ifs <;> simp
    · rw [ite_eq_right hx]
      exact BW_homMatrix_entry_natDegree_le_ite e k ωs f0 f1 (r i) x
  · rw [sum_boole, Nat.cast_id, Fin_sum_ite_lt_e_add_one]

open scoped BigOperators in
theorem Fin_sum_ite_lt_and_ne_eq_e (e k : ℕ) (j : Fin ((e + 1) + (e + k))) (hj : j.1 ≤ e) :
    #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e ∧ i ≠ j} = e := by
  have hEq : ({i : Fin ((e + 1) + (e + k)) | i.1 ≤ e ∧ i ≠ j} : Finset _) =
      ({i : Fin ((e + 1) + (e + k)) | i.1 ≤ e} : Finset _).erase j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    exact and_comm
  have hjS : j ∈ ({i : Fin ((e + 1) + (e + k)) | i.1 ≤ e} : Finset _) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩
  rw [hEq, Finset.card_erase_of_mem hjS, Fin_sum_ite_lt_e_add_one, Nat.add_sub_cancel]

open scoped BigOperators in
open Polynomial in
open Matrix in
theorem BW_homMatrix_det_updateCol_natDegree_le_of_lt {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F)
    (r : Fin ((e + 1) + (e + k)) → ι)
    (i0 : Fin ((e + 1) + (e + k)))
    (j : Fin ((e + 1) + (e + k))) (hj : j.1 < e + 1) :
    (Matrix.det
        (Matrix.updateCol
          (Matrix.submatrix
            (BW_homMatrix (ι := ι) e k
              (fun i => (Polynomial.C (ωs i) : F[X]))
              (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)))
            r id)
          j (Pi.single i0 (1 : F[X])))).natDegree ≤ e := by
  refine (natDegree_det_le_sum_of_natDegree_le _ (fun x ↦ if x.1 ≤ e ∧ x ≠ j then 1 else 0)
    fun i x ↦ ?_).trans_eq ?_
  · rw [Matrix.updateCol_apply]
    by_cases hx : x = j
    · rw [ite_eq_left hx, Pi.single_apply]
      split_ifs <;> simp
    · rw [ite_eq_right hx]
      refine (BW_homMatrix_entry_natDegree_le_ite e k ωs f0 f1 (r i) x).trans_eq ?_
      simp only [hx, ne_eq, not_false_eq_true, and_true]
  · rw [sum_boole, Nat.cast_id, Fin_sum_ite_lt_and_ne_eq_e e k j (by omega)]

omit [Fintype F] [DecidableEq ι] in
theorem RS_BW_bound_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F) (C := ReedSolomon.code domain deg)) :
    2 * Nat.floor (δ * Fintype.card ι) < Fintype.card ι - deg + 1 := by
  classical
  set n : ℕ := Fintype.card ι
  set e : ℕ := Nat.floor (δ * n)
  have hnpos : (0 : ℝ≥0) < (n : ℝ≥0) := by
    exact_mod_cast (Fintype.card_pos (α := ι))
  have he_le_mul : (e : ℝ≥0) ≤ δ * n := Nat.floor_le (by positivity)
  have he_div_le_δ : (e : ℝ≥0) / n ≤ δ := (div_le_iff₀ hnpos).2 he_le_mul
  have he_le_UDR : e ≤ Code.uniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg) :=
    (Code.dist_le_UDR_iff_relDist_le_relUDR
      (C := (ReedSolomon.code domain deg : Set (ι → F))) e).2 (he_div_le_δ.trans hδ)
  have hdist_eq : ‖(ReedSolomon.code domain deg : Set (ι → F))‖₀ = n - deg + 1 :=
    ReedSolomon.dist_eq_of_le (ι := ι) (F := F) (α := domain) (n := deg) hdeg
  have : NeZero (‖(ReedSolomon.code domain deg : Set (ι → F))‖₀) :=
    ⟨hdist_eq ▸ Nat.succ_ne_zero _⟩
  have htwo : 2 * e < ‖(ReedSolomon.code domain deg : Set (ι → F))‖₀ :=
    (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (e := e)).1 he_le_UDR
  rwa [hdist_eq] at htwo

open Matrix in
open Polynomial in
omit [Fintype F] [DecidableEq F] in
theorem RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F))
    (t : Fin (n + 1)) :
    B.adjugate t (Fin.last n) =
      (-1 : (Polynomial F)) ^ ((Fin.last n : ℕ) + (t : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]

open Matrix in
open Polynomial in
omit [Fintype F] [DecidableEq F] in
theorem RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F)) :
    B.adjugate (Fin.last n) (Fin.last n) =
      (-1 : (Polynomial F)) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
  -- apply the provided adjugate formula with t = Fin.last n
  rw [RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc, Fin.succAbove_last]

open Matrix in
open Polynomial in
omit [Fintype F] [DecidableEq F] in
theorem RS_det_submatrix_eq_zero_of_det_eq_zero (n : ℕ)
    (K : Matrix (Fin n) (Fin n) (Polynomial F))
    (hdet : Matrix.det K = 0)
    (I J : Fin n ↪ Fin n) :
    Matrix.det (K.submatrix I J) = 0 := by
  -- Self-embeddings of `Fin n` are permutations, and permuting rows or columns scales `det` by a
  -- sign.
  rw [show K.submatrix I J = (K.submatrix I.equivOfFiniteSelfEmbedding id).submatrix id
      J.equivOfFiniteSelfEmbedding from rfl, Matrix.det_permute', Matrix.det_permute, hdet,
    mul_zero, mul_zero]

omit [Fintype F] [DecidableEq ι] in
theorem RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg] (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg)) :
    Nat.floor (δ * Fintype.card ι) + deg ≤ Fintype.card ι := by
  have hBW := RS_BW_bound_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hdeg hδ
  omega

omit [Fintype F] [DecidableEq ι] in
theorem RS_floor_mul_card_ι_add_one_le_card_ι_of_le_relUDR {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg] (hdeg : deg ≤ Fintype.card ι)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg)) :
    Nat.floor (δ * Fintype.card ι) + 1 ≤ Fintype.card ι :=
  (Nat.add_le_add_left NeZero.one_le _).trans
    (RS_floor_mul_card_ι_add_deg_le_card_ι_of_le_relUDR hdeg hδ)

open Polynomial in
open Matrix in
omit [Fintype F] [DecidableEq F] in
theorem RS_isUnit_det_vandermonde_C_of_injective (n : ℕ) (v : Fin n → F)
    (hv : Function.Injective v) :
    IsUnit (Matrix.det (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X])))) := by
  classical
  -- The Vandermonde matrix over `F[X]` with constant entries is the entrywise image of the
  -- Vandermonde matrix over `F` under the ring hom `Polynomial.C`.
  have hdet :
      (Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X]))).det =
        (Polynomial.C : F →+* F[X]) ((Matrix.vandermonde v).det) := by
    have hvand :
        (Polynomial.C : F →+* F[X]).mapMatrix (Matrix.vandermonde v) =
          Matrix.vandermonde (fun i : Fin n => (Polynomial.C (v i) : F[X])) := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.vandermonde_apply, map_pow]
    -- Map the determinant through `Polynomial.C` and rewrite the mapped matrix as a Vandermonde.
    rw [← hvand, RingHom.map_det]
  -- Over a field, the Vandermonde determinant is nonzero iff the entries are distinct.
  have hne : (Matrix.vandermonde v).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  -- In a field, nonzero elements are units.
  have hunit : IsUnit ((Matrix.vandermonde v).det) := (isUnit_iff_ne_zero).2 hne
  -- Constant polynomials are units iff their coefficients are units.
  have hunitC : IsUnit ((Polynomial.C : F →+* F[X]) ((Matrix.vandermonde v).det)) :=
    (Polynomial.isUnit_C (x := (Matrix.vandermonde v).det)).2 hunit
  -- Conclude by rewriting the determinant as a constant polynomial.
  rw [hdet]
  exact hunitC

open Matrix in
open Polynomial in
omit [Fintype F] [DecidableEq F] in
theorem RS_mulVec_adjugate_col_eq_det (n : ℕ) (A : Matrix (Fin n) (Fin n) (Polynomial F))
    (j : Fin n) :
    Matrix.mulVec A (fun i : Fin n => A.adjugate i j) =
      (fun i : Fin n => if i = j then Matrix.det A else 0) := by
  classical
  funext i
  calc
    Matrix.mulVec A (fun k : Fin n => A.adjugate k j) i = (A * A.adjugate) i j := rfl
    _ = (A.det • (1 : Matrix (Fin n) (Fin n) (Polynomial F))) i j := by
      rw [Matrix.mul_adjugate]
    _ = (if i = j then Matrix.det A else 0) := by
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

open Matrix in
open Polynomial in
omit [Fintype F] [DecidableEq F] in
theorem RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Polynomial F)) (j : Fin n) (hdet : Matrix.det A = 0) :
    Matrix.mulVec A (fun i : Fin n => A.adjugate i j) = 0 := by
  classical
  -- Rewrite using the adjugate column identity
  rw [RS_mulVec_adjugate_col_eq_det n A j]
  -- Now simplify using det A = 0
  ext i
  by_cases h : i = j
  · simp [h, hdet]
  · simp [h]


open scoped BigOperators in
open Matrix in
theorem RS_mulVec_append_castAdd_natAdd {R : Type} [NonUnitalNonAssocSemiring R] {ι : Type}
    (m n : ℕ) (M : Matrix ι (Fin (m + n)) R) (a : Fin m → R) (b : Fin n → R) :
    Matrix.mulVec M (Fin.append a b) =
      Matrix.mulVec (M.submatrix id (Fin.castAdd n)) a +
        Matrix.mulVec (M.submatrix id (Fin.natAdd m)) b := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Matrix.submatrix_apply, Pi.add_apply, id_eq]

open Polynomial in
open Matrix in
omit [Fintype F] [DecidableEq F] in
theorem RS_natDegree_det_le_of_entry_natDegree_le_one (n : ℕ) (A : Matrix (Fin n) (Fin n) F[X])
    (hdeg : ∀ i j, (A i j).natDegree ≤ 1) :
    (Matrix.det A).natDegree ≤ n :=
  (natDegree_det_le_sum_of_natDegree_le A (fun _ ↦ 1) hdeg).trans_eq
    (by rw [Fin.sum_const, smul_eq_mul, mul_one])

open scoped BigOperators in
open Polynomial in
open Matrix in
omit [Fintype F] [DecidableEq F] in
theorem RS_natDegree_inv_neg_vandermonde_C_eq_zero (n : ℕ) (v : Fin n → F)
    (hv : Function.Injective v) :
    ∀ i j : Fin n,
      ((-Matrix.vandermonde (fun t : Fin n => (Polynomial.C (v t) : F[X])))⁻¹ i j).natDegree =
        0 := by
  classical
  intro i j
  let f : F →+* F[X] := Polynomial.C
  let D0 : Matrix (Fin n) (Fin n) F := -Matrix.vandermonde v
  let D : Matrix (Fin n) (Fin n) F[X] :=
    -Matrix.vandermonde (fun t : Fin n => (Polynomial.C (v t) : F[X]))
  change ((D⁻¹ i j).natDegree = 0)
  have hDmap : D = D0.map f := by
    ext i j
    simp only [D, D0, f, Matrix.map_apply, Matrix.neg_apply, Matrix.vandermonde_apply, map_neg,
      map_pow]
  have hdetV : (Matrix.det (Matrix.vandermonde v)) ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  have hdetD0 : (Matrix.det D0) ≠ 0 := by
    have h : ((-1 : F) ^ (Fintype.card (Fin n)) * Matrix.det (Matrix.vandermonde v)) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hdetV
    rwa [Matrix.det_neg]
  have hunit0 : IsUnit (Matrix.det D0) := (isUnit_iff_ne_zero).2 hdetD0
  have hmul0 : D0 * D0⁻¹ = 1 := Matrix.mul_nonsing_inv D0 hunit0
  have hmul : (D0.map f) * ((D0⁻¹).map f) = (1 : Matrix (Fin n) (Fin n) F[X]) := by
    rw [← Matrix.map_mul, hmul0, Matrix.map_one _ (map_zero f) (map_one f)]
  have hmul' : D * ((D0⁻¹).map f) = (1 : Matrix (Fin n) (Fin n) F[X]) := by
    rw [hDmap]
    exact hmul
  have hinv : D⁻¹ = (D0⁻¹).map f := by
    exact Matrix.inv_eq_right_inv (A := D) (B := (D0⁻¹).map f) hmul'
  simp [hinv, Matrix.map_apply, f]

open scoped BigOperators in
open Polynomial in
open Matrix in
omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
theorem RS_vandermonde_coeffs_eq_zero (m : ℕ) {domain : ι ↪ F} (hm : m ≤ Fintype.card ι)
    (b : Fin m → F[X]) :
    (∀ i : ι,
      (∑ s : Fin m, b s * (Polynomial.C (domain i) : F[X]) ^ s.1) = 0) →
    b = 0 := by
  classical
  intro h
  let r0 : Fin m ↪ ι :=
    (Fin.castLEEmb hm).trans ((Fintype.equivFin ι).symm.toEmbedding)
  let v : Fin m → F[X] := fun j => (Polynomial.C (domain (r0 j)) : F[X])
  let V : Matrix (Fin m) (Fin m) F[X] := Matrix.vandermonde v
  have hv : Function.Injective v := by
    intro j₁ j₂ hj
    apply r0.injective
    apply domain.injective
    exact Polynomial.C_injective hj
  have hdet : V.det ≠ 0 := (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  have hmul : V *ᵥ b = 0 := by
    funext j
    -- `mulVec` uses `∑ s, V j s * b s` while our hypothesis has `b s * ...`.
    exact (Finset.sum_congr rfl fun s _ ↦ mul_comm _ _).trans (h (r0 j))
  exact Matrix.eq_zero_of_mulVec_eq_zero (M := V) hdet hmul

open scoped BigOperators in
open Polynomial in
open Matrix in
omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
theorem RS_a_ne_zero_of_BW_homMatrix_mulVec_eq_zero {deg : ℕ} {domain : ι ↪ F} {e : ℕ}
    (u : WordStack F (Fin 2) ι)
    {a : Fin (e + 1) → F[X]} {b : Fin (e + deg) → F[X]}
    (hdeg : e + deg ≤ Fintype.card ι)
    (happend : Fin.append a b ≠ 0)
    (hMul :
      Matrix.mulVec
          (BW_homMatrix (ι := ι) e deg
            (fun i => (Polynomial.C (domain i) : F[X]))
            (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)))
          (Fin.append a b) = 0) :
    a ≠ 0 := by
  intro ha0
  -- Pointwise equality derived from the mulVec hypothesis
  have hEq :
      ∀ i : ι,
        (∑ t : Fin (e + 1), a t * (Polynomial.C (domain i) : F[X]) ^ t.1) *
            (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) =
          ∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1 :=
    (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (R := F[X]) e deg
          (fun i => (Polynomial.C (domain i) : F[X]))
          (fun i =>
            Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))
          a b).1 hMul
  have hVand :
      ∀ i : ι,
        (∑ s : Fin (e + deg), b s * (Polynomial.C (domain i) : F[X]) ^ s.1) = 0 := by
    intro i
    -- With a = 0, the left sum is 0, so the RHS must be 0.
    rw [← hEq i, ha0]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  have hb0 : b = 0 :=
    RS_vandermonde_coeffs_eq_zero (ι := ι) (F := F) (m := e + deg) (domain := domain) hdeg b hVand
  have happend0 : Fin.append a b = 0 := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, ha0, hb0, Pi.zero_apply]
  exact happend happend0

open Matrix in
theorem adjugate_updateRow_same_col {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (i j : n) (b : n → R) :
    (A.updateRow i b).adjugate j i = A.adjugate j i := by
  simp [Matrix.adjugate_apply]

open scoped BigOperators in
open Matrix in
theorem det_updateRow_eq_sum_mul_adjugate_col {R : Type} [CommRing R] {n : Type} [Fintype n]
    [DecidableEq n] (A : Matrix n n R) (i : n) (b : n → R) :
    (A.updateRow i b).det = ∑ j : n, b j * A.adjugate j i := by
  classical
  -- Laplace expansion of the determinant along the updated row
  simpa [Matrix.updateRow_apply, adjugate_updateRow_same_col, mul_assoc] using
    (Matrix.det_eq_sum_mul_adjugate_row (A := A.updateRow i b) (i := i))


open scoped BigOperators in
open Polynomial in
open Matrix in
omit [Nonempty ι] [Fintype F] [DecidableEq ι] [DecidableEq F] in
theorem RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one (e : ℕ)
    (K : Matrix ι (Fin (e + 1)) F[X])
    (hcard : e + 1 ≤ Fintype.card ι)
    (hdeg : ∀ i j, (K i j).natDegree ≤ 1)
    (hdet : ∀ r : Fin (e + 1) → ι, Matrix.det (K.submatrix r id) = 0) :
    ∃ a : Fin (e + 1) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧ Matrix.mulVec K a = 0 := by
  classical
  let n : ℕ := e + 1
  let P : ℕ → Prop := fun r =>
    ∃ (I : Fin r ↪ ι) (J : Fin r ↪ Fin n), Matrix.det (K.submatrix I J) ≠ (0 : F[X])
  let : DecidablePred P := Classical.decPred _
  have P0 : P 0 := by
    refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
    rw [Matrix.det_isEmpty]
    exact @one_ne_zero F[X] _ _ NeZero.one
  let r : ℕ := Nat.findGreatest P n
  have Pr : P r := Nat.findGreatest_spec (P := P) (n := n) (m := 0) (Nat.zero_le n) P0
  rcases Pr with ⟨I, J, hdetIJ⟩
  have hnotPn : ¬ P n := by
    intro hPn
    rcases hPn with ⟨I0, J0, hdet0⟩
    let A : Matrix (Fin n) (Fin n) F[X] := K.submatrix I0 id
    have hdetA : Matrix.det A = 0 := by
      simpa [A] using hdet I0
    have hdet_sub : Matrix.det (A.submatrix (Function.Embedding.refl _) J0) = 0 :=
      RS_det_submatrix_eq_zero_of_det_eq_zero n A hdetA (Function.Embedding.refl _) J0
    have hdetK : Matrix.det (K.submatrix I0 J0) = 0 := by
      have hmatrix : K.submatrix I0 J0 = A.submatrix (Function.Embedding.refl _) J0 := by
        ext i j
        rfl
      rw [hmatrix]
      exact hdet_sub
    exact hdet0 hdetK
  have hrle : r ≤ n := Nat.findGreatest_le (P := P) n
  have hrne : r ≠ n := by
    intro hre
    have hcond : n ≠ 0 → P n :=
      (Nat.findGreatest_eq_iff (P := P) (k := n) (m := n)).1 hre |>.2.1
    exact hnotPn (hcond (Nat.succ_ne_zero e))
  have hrlt : r < n := Nat.lt_of_le_of_ne hrle hrne
  have hrle_e : r ≤ e := Nat.lt_succ_iff.mp hrlt
  have hcard' : n ≤ Fintype.card ι := hcard
  have hrltcardι : r < Fintype.card ι := lt_of_lt_of_le hrlt hcard'
  -- pick i0 ∉ range I
  let sI : Finset ι := Finset.univ.map I
  have hsIlt : sI.card < (Finset.univ : Finset ι).card := by
    rw [Finset.card_map, Finset.card_univ, Finset.card_univ, Fintype.card_fin]
    exact hrltcardι
  obtain ⟨i0, -, hi0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsIlt
  have hi0 : i0 ∉ Set.range I := by
    intro hi
    rcases hi with ⟨i, rfl⟩
    apply hi0_notmem
    refine Finset.mem_map.2 ?_
    exact ⟨i, Finset.mem_univ _, rfl⟩
  -- pick j0 ∉ range J
  let sJ : Finset (Fin n) := Finset.univ.map J
  have hsJlt : sJ.card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_map, Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    exact hrlt
  obtain ⟨j0, -, hj0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsJlt
  have hj0 : j0 ∉ Set.range J := by
    intro hj
    rcases hj with ⟨j, rfl⟩
    apply hj0_notmem
    refine Finset.mem_map.2 ?_
    exact ⟨j, Finset.mem_univ _, rfl⟩
  let I' : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi0
  let J' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc J hj0
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := K.submatrix I' J'
  have hnotPr1 : ¬ P (r + 1) := by
    have hk : Nat.findGreatest P n < r + 1 := Nat.lt_succ_self _
    have hkb : r + 1 ≤ n := Nat.succ_le_of_lt hrlt
    exact Nat.findGreatest_is_greatest (P := P) (n := n) (k := r + 1) hk hkb
  have hdetB : Matrix.det B = 0 := by
    by_contra hne
    have : P (r + 1) := ⟨I', J', hne⟩
    exact hnotPr1 this
  let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)
  have hBu : Matrix.mulVec B u = 0 :=
    RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB
  have hsub_cast : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
    funext i j
    simp only [B, I', J', Matrix.submatrix_apply, Fin.Embedding.snoc_castSucc]
  have hu_last : u (Fin.last r) =
      (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) :=
    RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)
  have hu_last_ne : u (Fin.last r) ≠ (0 : F[X]) := by
    have hsign : (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) ≠ (0 : F[X]) := by
      exact pow_ne_zero _ (neg_ne_zero.2 (@one_ne_zero F[X] _ _ NeZero.one))
    have hdetMinor : Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) ≠ (0 : F[X]) := by
      rw [hsub_cast]
      exact hdetIJ
    rw [hu_last]
    exact mul_ne_zero hsign hdetMinor
  -- degree bound on u
  have hdeg_u : ∀ t : Fin (r + 1), (u t).natDegree ≤ r := by
    intro t
    have hu_t : u t =
        (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
          Matrix.det (B.submatrix Fin.castSucc t.succAbove) :=
      RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)
    have hdeg_det : (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ r :=
      -- entries come from K
      RS_natDegree_det_le_of_entry_natDegree_le_one (n := r)
        (A := B.submatrix Fin.castSucc t.succAbove) fun i j ↦
          hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))
    have hdeg_sign : ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree = 0 := by
      rw [← C_1, ← C_neg, ← C_pow, natDegree_C]
    rw [hu_t]
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [hdeg_sign, zero_add]
    exact hdeg_det
  -- extend u to all columns
  let a : Fin n → F[X] := Function.extend (J' : Fin (r + 1) → Fin n) u (fun _ => 0)
  have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := fun t ↦
    J'.injective.extend_apply u (fun _ => 0) t
  have ha_off : ∀ j : Fin n, (¬∃ t : Fin (r + 1), J' t = j) → a j = 0 := fun j hj ↦
    Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0) j hj
  have ha_ne : a ≠ 0 := fun ha0 ↦
    hu_last_ne ((ha_on (Fin.last r)).symm.trans (congrFun ha0 (J' (Fin.last r))))
  have hdeg_a : ∀ j : Fin n, (a j).natDegree ≤ e := by
    intro j
    by_cases hj : ∃ t : Fin (r + 1), J' t = j
    · rcases hj with ⟨t, rfl⟩
      rw [ha_on t]
      exact (hdeg_u t).trans hrle_e
    · rw [ha_off j hj, natDegree_zero]
      exact Nat.zero_le e
  have hmul_formula (i : ι) : Matrix.mulVec K a i = ∑ t : Fin (r + 1), K i (J' t) * u t := by
    have hsum : (∑ t : Fin (r + 1), K i (J' t) * u t) = ∑ j : Fin n, K i j * a j := by
      refine (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin n)) (he := J'.injective)
        (f := fun t : Fin (r + 1) => K i (J' t) * u t)
        (g := fun j : Fin n => K i j * a j) ?_ ?_)
      · intro j hj
        rw [ha_off j hj, mul_zero]
      · intro t
        rw [ha_on t]
    change (∑ j, K i j * a j) = ∑ t, K i (J' t) * u t
    exact hsum.symm
  have hmulVec : Matrix.mulVec K a = 0 := by
    funext i
    by_cases hi : i ∈ Set.range I
    · rcases hi with ⟨t, rfl⟩
      have hrow : (∑ x, B (Fin.castSucc t) x * u x) = 0 := congrFun hBu (Fin.castSucc t)
      simp only [B, I', Matrix.submatrix_apply, Fin.Embedding.snoc_castSucc] at hrow
      exact (hmul_formula (I t)).trans hrow
    · -- i ∉ range I
      have hi' : i ∉ Set.range I := hi
      let Ii : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi'
      have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
        by_contra hne
        have : P (r + 1) := ⟨Ii, J', hne⟩
        exact hnotPr1 this
      let b : Fin (r + 1) → F[X] := fun j => K i (J' j)
      have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
        funext x
        funext y
        refine Fin.lastCases (motive := fun x => (B.updateRow (Fin.last r) b) x y =
            (K.submatrix Ii J') x y) ?_ ?_ x
        · -- x = last
          simp only [Matrix.updateRow_apply, ite_eq_left, b, Matrix.submatrix_apply,
            Ii, Fin.Embedding.snoc_last]
        · intro x
          simp only [Matrix.updateRow_apply, Fin.castSucc_ne_last, ite_false, B, I', Ii,
            Matrix.submatrix_apply, Fin.Embedding.snoc_castSucc]
      have hdet_update : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
        rw [hupdate]
        exact hdetBi
      have hsum0 : (∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r)) = 0 :=
        (det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)).symm.trans
          hdet_update
      exact (hmul_formula i).trans hsum0
  exact ⟨a, ha_ne, hdeg_a, hmulVec⟩

open Polynomial in
open Matrix in
omit [Fintype F] [DecidableEq F] in
theorem RS_exists_nonzero_kernelVec_of_det_eq_zero_natDegree_le_one (e : ℕ)
    (K : Matrix (Fin (e + 1)) (Fin (e + 1)) F[X])
    (hdeg : ∀ i j, (K i j).natDegree ≤ 1)
    (hdet : Matrix.det K = 0) :
    ∃ a : Fin (e + 1) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧ Matrix.mulVec K a = 0 := by
  refine RS_exists_nonzero_kernelVec_of_det_submatrix_eq_zero_natDegree_le_one e K
    (Fintype.card_fin _).ge hdeg fun r ↦ ?_
  by_cases hr : Function.Injective r
  · exact RS_det_submatrix_eq_zero_of_det_eq_zero _ K hdet ⟨r, hr⟩ (Function.Embedding.refl _)
  · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hr
    exact Matrix.det_zero_of_row_eq hne
      (funext fun _ ↦ by rw [submatrix_apply, submatrix_apply, hij])

end CoreResults

end ProximityGap

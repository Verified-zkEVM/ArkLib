/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Prelude
import ArkLib.Data.CodingTheory.ReedSolomon

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
theorem BW_homMatrix_entry_natDegree_eq_zero_of_ge_comm {F : Type} [Field F] {ι : Type} [Fintype ι]
    (e k : ℕ) (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) (hj : e + 1 ≤ j.1) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X) i j).natDegree = 0 := by
  have h :=
    BW_homMatrix_entry_natDegree_eq_zero_of_ge (ι := ι) (F := F) e k ωs f0 f1 i j hj
  have hfun :
      (fun i : ι => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
        = (fun i : ι => Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X) := by
    funext i'
    rw [mul_comm Polynomial.X (Polynomial.C (f1 i'))]
  -- rewrite the auxiliary lemma with the commuting multiplication
  simpa [hfun] using h


open Polynomial in
theorem BW_homMatrix_entry_natDegree_le_one {F : Type} [Field F] {ι : Type} [Fintype ι] (e k : ℕ)
    (ωs : ι → F) (f0 f1 : ι → F) (i : ι)
    (j : Fin ((e + 1) + (e + k))) :
    (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
        (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i)) i j).natDegree ≤ 1 := by
  classical
  by_cases hjle : (j.1 ≤ e)
  · -- j.1 ≤ e
    simp only [BW_homMatrix, Order.lt_add_one_iff, X_mul_C, Matrix.of_apply, hjle, ↓reduceIte]
    have hlin :
        (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤ 1 := by
      have hadd :
          (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤
            max (Polynomial.C (f0 i) : F[X]).natDegree
              (Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree := by
        exact
          (Polynomial.natDegree_add_le (Polynomial.C (f0 i) : F[X])
            (Polynomial.C (f1 i) * Polynomial.X : F[X]))
      have hC : (Polynomial.C (f0 i) : F[X]).natDegree ≤ 1 := by
        simp
      have hX : (Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree ≤ 1 := by
        simpa using Polynomial.natDegree_mul_le
          (p := (Polynomial.C (f1 i) : F[X])) (q := (Polynomial.X : F[X]))
      exact le_trans hadd (max_le hC hX)
    have hq : ((Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree = 0 := by
      simp
    calc
      ((Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]) *
            (Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree ≤
          (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree +
            ((Polynomial.C (ωs i) : F[X]) ^ j.1).natDegree :=
        Polynomial.natDegree_mul_le
          (p := (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]))
          (q := (Polynomial.C (ωs i) : F[X]) ^ j.1)
      _ = (Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X : F[X]).natDegree := by
        simp [hq]
      _ ≤ 1 := hlin
  · -- ¬ j.1 ≤ e
    simp [BW_homMatrix, hjle]

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
  constructor
  · intro h i
    have hi := congrArg (fun v => v i) h
    have hi' :
        (∑ j : Fin ((e + 1) + (e + k)),
            BW_homMatrix (ι := ι) e k ωs f i j * Fin.append a b j) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using hi
    have hi'' := hi'
    rw [Fin.sum_univ_add] at hi''
    simp only [BW_homMatrix, Order.lt_add_one_iff, Matrix.of_apply, Fin.val_castAdd, hx,
      ↓reduceIte, Fin.append_left, Fin.val_natAdd, hy, add_tsub_cancel_left, Fin.append_right,
      neg_mul, sum_neg_distrib] at hi''
    have hAC :
        (∑ x : Fin (e + 1), f i * ωs i ^ x.1 * a x) =
          ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
      have := eq_neg_of_add_eq_zero_left hi''
      simpa using this
    -- Convert `hAC` into the desired coefficientwise identity.
    calc
      (∑ t : Fin (e + 1), a t * ωs i ^ t.1) * f i
          = f i * (∑ t : Fin (e + 1), a t * ωs i ^ t.1) := by
              simp [mul_comm]
      _ = ∑ t : Fin (e + 1), f i * (a t * ωs i ^ t.1) := by
              simp [Finset.mul_sum]
      _ = ∑ t : Fin (e + 1), f i * ωs i ^ t.1 * a t := by
              simp [mul_left_comm, mul_comm]
      _ = ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
              simpa using hAC
      _ = ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
              simp [mul_comm]
  · intro h
    ext i
    -- expand the matrix-vector multiplication at coordinate `i`
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Fin.sum_univ_add]
    simp only [BW_homMatrix, Order.lt_add_one_iff, Matrix.of_apply, Fin.val_castAdd, hx,
      ↓reduceIte, Fin.append_left, Fin.val_natAdd, hy, add_tsub_cancel_left, Fin.append_right,
      neg_mul, sum_neg_distrib]
    -- turn the hypothesis `h i` into the same normal form
    have hEq0 : f i * (∑ t : Fin (e + 1), a t * ωs i ^ t.1) =
        ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
      simpa [mul_comm] using h i
    have hEq1 : (∑ t : Fin (e + 1), f i * (a t * ωs i ^ t.1)) =
        ∑ s : Fin (e + k), b s * ωs i ^ s.1 := by
      simpa [Finset.mul_sum] using hEq0
    have hAC :
        (∑ x : Fin (e + 1), f i * ωs i ^ x.1 * a x) =
          ∑ x : Fin (e + k), ωs i ^ x.1 * b x := by
      -- rearrange products in `hEq1`
      simpa [mul_assoc, mul_left_comm, mul_comm]
    -- use `hAC` to close the goal
    simp [hAC]

open scoped BigOperators in
theorem Fin_sum_ite_lt_e_add_one (e k : ℕ) :
    #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e} = e + 1 := by
  classical
  have hle : e + 1 ≤ (e + 1) + (e + k) := Nat.le_add_right (e + 1) (e + k)
  have hcard_lt0 :
      Fintype.card {i : Fin ((e + 1) + (e + k)) // i.1 < e + 1} = e + 1 :=
    Fintype.card_fin_lt_of_le (m := e + 1) (n := (e + 1) + (e + k)) hle
  have hcard_lt : #{i : Fin ((e + 1) + (e + k)) | i.1 < e + 1} = e + 1 := by
    simpa [Fintype.card_subtype] using hcard_lt0
  simpa [Nat.lt_succ_iff] using hcard_lt

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
  classical
  -- Name the matrices to keep subsequent expressions manageable.
  let M : Matrix ι (Fin ((e + 1) + (e + k))) F[X] :=
    BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
      (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
  let A : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.submatrix M r id
  change (Matrix.det A).natDegree ≤ e + 1
  -- Expand determinant as a sum over permutations.
  rw [Matrix.det_apply]
  refine
    (Polynomial.natDegree_sum_le_of_forall_le
        (s :=
          (Finset.univ : Finset (Equiv.Perm (Fin ((e + 1) + (e + k))))))
        (f := fun σ : Equiv.Perm (Fin ((e + 1) + (e + k))) =>
          Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), A (σ i) i)
        (n := e + 1) ?_)
  intro σ hσ
  -- The permutation sign is a unit (±1), so it does not increase natDegree.
  have hsign :
      (Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree ≤
        (∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  -- Degree of a product is bounded by the sum of degrees.
  have hprod :
      (∏ i : Fin ((e + 1) + (e + k)), A (σ i) i).natDegree ≤
        ∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree := by
    simpa using
      (Polynomial.natDegree_prod_le
        (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
        (f := fun i : Fin ((e + 1) + (e + k)) => A (σ i) i))
  -- Only the first `e+1` columns can contribute degree (and each contributes at most 1).
  have hsum :
      (∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree) ≤ e + 1 := by
    have hpoint :
        ∀ i : Fin ((e + 1) + (e + k)),
          (A (σ i) i).natDegree ≤ ite (i.1 < e + 1) (1 : ℕ) 0 := by
      intro i
      by_cases hi : i.1 < e + 1
      · -- In the first `e+1` columns, each entry has natDegree ≤ 1.
        have hle1 :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
                (r (σ i)) i).natDegree ≤ 1 :=
          BW_homMatrix_entry_natDegree_le_one (ι := ι) (F := F) e k ωs f0 f1
            (r (σ i)) i
        simpa [A, M, Matrix.submatrix, hi] using hle1
      · -- After column `e+1`, the entry is constant in `X`, hence natDegree = 0.
        have hi' : e + 1 ≤ i.1 := Nat.le_of_not_gt hi
        have hzero :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.C (f1 i) * Polynomial.X)
                (r (σ i)) i).natDegree = 0 :=
          BW_homMatrix_entry_natDegree_eq_zero_of_ge_comm (ι := ι) (F := F) e k ωs
            f0 f1 (r (σ i)) i hi'
        have hzero' :
            (BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
                (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
                (r (σ i)) i).natDegree = 0 := by
          -- For these columns, the definition of `BW_homMatrix` ignores the input `f`.
          simpa [BW_homMatrix, Nat.not_lt_of_ge hi'] using hzero
        have hA : (A (σ i) i).natDegree = 0 := by
          simpa [A, M, Matrix.submatrix] using hzero'
        simp [hi, hA]
    have hle :
        (∑ i : Fin ((e + 1) + (e + k)), (A (σ i) i).natDegree)
          ≤
          ∑ i : Fin ((e + 1) + (e + k)), ite (i.1 < e + 1) (1 : ℕ) 0 := by
      simpa using
        (Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (fun i _ => hpoint i))
    -- `simp` rewrites this indicator sum into a cardinality, so rewrite the axiom the same way.
    have hcard :
        (#{x : Fin ((e + 1) + (e + k)) | (x.1 : ℕ) ≤ e} : ℕ) = e + 1 := by
      simpa [Nat.lt_succ_iff] using Fin_sum_ite_lt_e_add_one e k
    -- Conclude.
    simpa [hcard] using hle
  -- Assemble the inequalities.
  exact le_trans hsign (le_trans hprod hsum)


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
  classical
  let A : Matrix ι (Fin ((e + 1) + (e + k))) F[X] :=
    BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
      (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
  let B : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.submatrix A r id
  let B' : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.updateCol B j (Pi.single i0 (1 : F[X]))
  have hB' : (Matrix.det B').natDegree ≤ e + 1 := by
    -- Expand the determinant using Leibniz formula
    rw [Matrix.det_apply]
    -- Bound the natDegree of the sum by bounding each summand
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := (Finset.univ : Finset (Equiv.Perm (Fin ((e + 1) + (e + k))))))
        (n := e + 1)
        (f := fun σ : Equiv.Perm (Fin ((e + 1) + (e + k))) =>
          Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i)
        ?_
    intro σ hσ
    -- Ignore the sign: it is ±1, so it does not increase natDegree
    have hsign :
        (Equiv.Perm.sign σ •
              ∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree ≤
            (∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · simp [hs]
      · simp [hs, Units.neg_smul]
    -- Bound degree of the product by the sum of degrees
    have hprod :
        (∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree ≤
            ∑ i : Fin ((e + 1) + (e + k)), (B' (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (f := fun i : Fin ((e + 1) + (e + k)) => B' (σ i) i))
    -- Bound each factor's natDegree by an indicator for the first (e+1) columns
    have hsum :
        (∑ i : Fin ((e + 1) + (e + k)), (B' (σ i) i).natDegree) ≤
            ∑ i : Fin ((e + 1) + (e + k)), if i.1 ≤ e then (1 : ℕ) else 0 := by
      classical
      simpa using
        (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (f := fun i : Fin ((e + 1) + (e + k)) => (B' (σ i) i).natDegree)
          (g := fun i : Fin ((e + 1) + (e + k)) => if i.1 ≤ e then (1 : ℕ) else 0)
          (by
            intro i hi
            by_cases hij : i = j
            · -- updated column: entries are `Pi.single`, hence constant
              have hval : B' (σ i) i =
                  ((Pi.single i0 (1 : F[X])) : Fin ((e + 1) + (e + k)) → F[X]) (σ i) := by
                simp [B', hij.symm]
              have hdeg : (B' (σ i) i).natDegree = 0 := by
                -- reduce to a constant polynomial (either `1` or `0`)
                rw [hval]
                by_cases hsi : σ i = i0
                · -- hit the support
                  rw [hsi]
                  simp
                · -- miss the support
                  have :
                      ((Pi.single i0 (1 : F[X])) : Fin ((e + 1) + (e + k)) → F[X]) (σ i) = 0 := by
                    simp [Pi.single, hsi]
                  simp [this]
              have hi0 : ¬(i.1 ≤ e) := by
                have hge : e + 1 ≤ i.1 := by
                  simpa [hij] using hj
                exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self e) hge)
              simp [hdeg, hi0]
            · -- non-updated column
              have hentry : (B' (σ i) i).natDegree = (A (r (σ i)) i).natDegree := by
                simp [B', B, hij]
              by_cases hi0 : i.1 ≤ e
              · have hle : (A (r (σ i)) i).natDegree ≤ 1 := by
                  simpa [A] using
                    (BW_homMatrix_entry_natDegree_le_one (ι := ι) (F := F) e k ωs f0 f1
                      (r (σ i)) i)
                have : (B' (σ i) i).natDegree ≤ 1 := by
                  simpa [hentry] using hle
                simpa [hi0] using this
              · have hig : e + 1 ≤ i.1 := by
                  exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hi0)
                have hdeg0 : (A (r (σ i)) i).natDegree = 0 := by
                  simpa [A] using
                    (BW_homMatrix_entry_natDegree_eq_zero_of_ge (ι := ι) (F := F) e k ωs f0 f1
                      (r (σ i)) i hig)
                have : (B' (σ i) i).natDegree = 0 := by
                  simpa [hentry] using hdeg0
                simp [this, hi0]))
    -- Evaluate the indicator sum using the provided counting lemma
    have hcount :
        (∑ i : Fin ((e + 1) + (e + k)), if i.1 ≤ e then (1 : ℕ) else 0) = e + 1 := by
      classical
      have :
          (∑ i : Fin ((e + 1) + (e + k)), if i.1 ≤ e then (1 : ℕ) else 0) =
            #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e} := by
        simp
      simpa [this] using (Fin_sum_ite_lt_e_add_one (e := e) (k := k))
    -- Put everything together
    have :
        (Equiv.Perm.sign σ •
              ∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree ≤ e + 1 := by
      calc
        (Equiv.Perm.sign σ •
              ∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree ≤
            (∏ i : Fin ((e + 1) + (e + k)), B' (σ i) i).natDegree := hsign
        _ ≤ ∑ i : Fin ((e + 1) + (e + k)), (B' (σ i) i).natDegree := hprod
        _ ≤ ∑ i : Fin ((e + 1) + (e + k)), if i.1 ≤ e then (1 : ℕ) else 0 := hsum
        _ = e + 1 := hcount
    simpa using this
  simpa [A, B, B'] using hB'

open scoped BigOperators in
theorem Fin_sum_ite_lt_and_ne_eq_e (e k : ℕ) (j : Fin ((e + 1) + (e + k))) (hj : j.1 ≤ e) :
    #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e ∧ i ≠ j} = e := by
  classical
  -- Let `n := (e+1) + (e+k)` and `S := {i : Fin n | i.1 ≤ e}`.
  let S : Finset (Fin ((e + 1) + (e + k))) := {i : Fin ((e + 1) + (e + k)) | i.1 ≤ e}
  have hScard : S.card = e + 1 := by
    simpa [S] using (Fin_sum_ite_lt_e_add_one e k)
  have hjS : j ∈ S := by
    simpa [S] using hj
  have hErase : (S.erase j).card = e := by
    calc
      (S.erase j).card = S.card - 1 := Finset.card_erase_of_mem hjS
      _ = (e + 1) - 1 := by simp [hScard]
      _ = e := by simp
  have hEq : ({i : Fin ((e + 1) + (e + k)) | i.1 ≤ e ∧ i ≠ j} : Finset (Fin ((e + 1) + (e + k)))) =
      S.erase j := by
    ext i
    by_cases hij : i = j
    · subst hij
      simp [S]
    · simp [S, hij, Finset.mem_erase, and_comm]
  -- Rewrite the goal using the identification with `S.erase j`.
  simpa [hEq] using hErase

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
  classical
  -- Abbreviations for the matrices involved
  let A : Matrix ι (Fin ((e + 1) + (e + k))) F[X] :=
    BW_homMatrix (ι := ι) e k (fun i => (Polynomial.C (ωs i) : F[X]))
      (fun i => Polynomial.C (f0 i) + Polynomial.X * Polynomial.C (f1 i))
  let B : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.submatrix A r id
  let M : Matrix (Fin ((e + 1) + (e + k))) (Fin ((e + 1) + (e + k))) F[X] :=
    Matrix.updateCol B j (Pi.single i0 (1 : F[X]))
  have hmain : (Matrix.det M).natDegree ≤ e := by
    -- Expand determinant via Leibniz formula and bound degrees termwise
    rw [Matrix.det_apply]
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s :=
          (Finset.univ :
            Finset (Equiv.Perm (Fin ((e + 1) + (e + k))))))
        (n := e)
        (f := fun σ : Equiv.Perm (Fin ((e + 1) + (e + k))) =>
          Equiv.Perm.sign σ •
            ∏ i : Fin ((e + 1) + (e + k)), M (σ i) i)
        ?_
    intro σ hσ
    -- the sign scalar does not increase natDegree
    have hsmul :
        (Equiv.Perm.sign σ •
              ∏ i : Fin ((e + 1) + (e + k)), M (σ i) i).natDegree ≤
          (∏ i : Fin ((e + 1) + (e + k)), M (σ i) i).natDegree :=
      Polynomial.natDegree_smul_le (a := Equiv.Perm.sign σ)
        (p := ∏ i : Fin ((e + 1) + (e + k)), M (σ i) i)
    refine hsmul.trans ?_
    -- bound degree of product by sum of degrees
    have hprod :
        (∏ i : Fin ((e + 1) + (e + k)), M (σ i) i).natDegree ≤
          ∑ i : Fin ((e + 1) + (e + k)), (M (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (f := fun i : Fin ((e + 1) + (e + k)) => M (σ i) i))
    refine hprod.trans ?_
    -- degree bound for each factor depending on the column
    have hterm :
        ∀ i : Fin ((e + 1) + (e + k)),
          (M (σ i) i).natDegree ≤ (if (i.1 ≤ e ∧ i ≠ j) then 1 else 0) := by
      intro i
      by_cases hij : i = j
      · -- updated column: the entry is 0 or 1, hence natDegree 0
        have hdeg0 : (M (σ i) i).natDegree = 0 := by
          by_cases hrow : σ j = i0
          · simp [M, B, hij, Pi.single, hrow]
          · simp [M, B, hij, Pi.single, hrow]
        simpa [hij] using (le_of_eq hdeg0)
      · by_cases hle : i.1 ≤ e
        · have hdeg : (A (r (σ i)) i).natDegree ≤ 1 := by
            simpa [A] using
              (BW_homMatrix_entry_natDegree_le_one (e := e) (k := k) (ωs := ωs)
                (f0 := f0) (f1 := f1) (i := r (σ i)) (j := i))
          have hdeg' : (M (σ i) i).natDegree ≤ 1 := by
            simpa [M, B, Matrix.updateCol_apply, hij, Matrix.submatrix_apply, A] using hdeg
          simpa [hle, hij] using hdeg'
        · have hlt : e < i.1 := Nat.lt_of_not_ge hle
          have hge : e + 1 ≤ i.1 := Nat.succ_le_of_lt hlt
          have hdeg0 : (A (r (σ i)) i).natDegree = 0 := by
            simpa [A] using
              (BW_homMatrix_entry_natDegree_eq_zero_of_ge (e := e) (k := k) (ωs := ωs)
                (f0 := f0) (f1 := f1) (i := r (σ i)) (j := i) hge)
          have hdeg0' : (M (σ i) i).natDegree = 0 := by
            simpa [M, B, Matrix.updateCol_apply, hij, Matrix.submatrix_apply, A] using hdeg0
          simpa [hle, hij] using (le_of_eq hdeg0')
    have hsum_indicator :
        (∑ i : Fin ((e + 1) + (e + k)), (M (σ i) i).natDegree) ≤
          ∑ i : Fin ((e + 1) + (e + k)),
            (if (i.1 ≤ e ∧ i ≠ j) then 1 else 0) := by
      classical
      simpa using
        (Finset.sum_le_sum
          (s := (Finset.univ : Finset (Fin ((e + 1) + (e + k)))))
          (fun i hi => hterm i))
    have hjle : j.1 ≤ e := Nat.lt_succ_iff.mp hj
    have hindicator_sum :
        (∑ i : Fin ((e + 1) + (e + k)),
            (if (i.1 ≤ e ∧ i ≠ j) then 1 else 0 : ℕ)) = e := by
      classical
      have hsum_card :
          (∑ i : Fin ((e + 1) + (e + k)),
              (if (i.1 ≤ e ∧ i ≠ j) then 1 else 0 : ℕ)) =
            #{i : Fin ((e + 1) + (e + k)) | i.1 ≤ e ∧ i ≠ j} := by
        simp
      simpa [hsum_card] using
        (Fin_sum_ite_lt_and_ne_eq_e (e := e) (k := k) (j := j) hjle)
    -- combine the bounds
    simpa [hindicator_sum] using hsum_indicator
  simpa [A, B, M] using hmain

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
  have he_le_mul : (e : ℝ≥0) ≤ δ * n := by
    simpa [e] using (Nat.floor_le (a := δ * n) (ha := by positivity))
  have he_div_le_δ : (e : ℝ≥0) / n ≤ δ := by
    -- `div_le_iff₀` works in `ℝ≥0` as `n > 0`
    exact (div_le_iff₀ hnpos).2 he_le_mul
  have he_div_le_relUDR : (e : ℝ≥0) / n ≤
      Code.relativeUniqueDecodingRadius (ι := ι) (F := F)
        (C := ReedSolomon.code domain deg) :=
    le_trans he_div_le_δ hδ
  have he_le_UDR : e ≤ Code.uniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg) := by
    exact (Code.dist_le_UDR_iff_relDist_le_relUDR
      (C := (ReedSolomon.code domain deg : Set (ι → F))) e).2 he_div_le_relUDR
  have hdist_pos : 0 < n - deg + 1 := by
    omega
  have hdist_ne : (‖(ReedSolomon.code domain deg : Set (ι → F))‖₀) ≠ 0 := by
    have hdist_eq : ‖(ReedSolomon.code domain deg : Set (ι → F))‖₀ = n - deg + 1 := by
      simpa [n] using
        (ReedSolomon.dist_eq' (ι := ι) (F := F) (α := domain) (n := deg) hdeg)
    simp [hdist_eq]
  haveI : NeZero (‖(ReedSolomon.code domain deg : Set (ι → F))‖₀) := ⟨hdist_ne⟩
  have htwo : 2 * e < ‖(ReedSolomon.code domain deg : Set (ι → F))‖₀ := by
    exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (e := e)).1 he_le_UDR
  have hdist_eq : ‖(ReedSolomon.code domain deg : Set (ι → F))‖₀ = n - deg + 1 := by
    simpa [n] using
      (ReedSolomon.dist_eq' (ι := ι) (F := F) (α := domain) (n := deg) hdeg)
  simpa [n, e, hdist_eq] using htwo

open Matrix in
open Polynomial in
omit [Fintype F] [DecidableEq F] in
theorem RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F))
    (t : Fin (n + 1)) :
    B.adjugate t (Fin.last n) =
      (-1 : (Polynomial F)) ^ ((Fin.last n : ℕ) + (t : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
  simpa [Fin.succAbove_last] using
    (Matrix.adjugate_fin_succ_eq_det_submatrix (A := B) (i := t) (j := Fin.last n))

open Matrix in
open Polynomial in
omit [Fintype F] [DecidableEq F] in
theorem RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F)) :
    B.adjugate (Fin.last n) (Fin.last n) =
      (-1 : (Polynomial F)) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
  -- apply the provided adjugate formula with t = Fin.last n
  simpa using
    (RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := n) (B := B) (t := Fin.last n))

open Matrix in
open Polynomial in
omit [Fintype F] [DecidableEq F] in
theorem RS_det_submatrix_eq_zero_of_det_eq_zero (n : ℕ)
    (K : Matrix (Fin n) (Fin n) (Polynomial F))
    (hdet : Matrix.det K = 0)
    (I J : Fin n ↪ Fin n) :
    Matrix.det (K.submatrix I J) = 0 := by
  classical
  let eI : Fin n ≃ Fin n := I.equivOfFiniteSelfEmbedding
  let eJ : Fin n ≃ Fin n := J.equivOfFiniteSelfEmbedding
  have hI : (eI.toEmbedding : Fin n ↪ Fin n) = I := by
    simp [eI]
  have hJ : (eJ.toEmbedding : Fin n ↪ Fin n) = J := by
    simp [eJ]
  have hsub : K.submatrix I J = K.submatrix eI eJ := by
    ext i j
    have hIi : eI i = I i := by
      have := congrArg (fun f : Fin n ↪ Fin n => f i) hI
      simpa [Equiv.toEmbedding_apply] using this
    have hJj : eJ j = J j := by
      have := congrArg (fun f : Fin n ↪ Fin n => f j) hJ
      simpa [Equiv.toEmbedding_apply] using this
    simp [Matrix.submatrix_apply, hIi, hJj]
  calc
    Matrix.det (K.submatrix I J) = Matrix.det (K.submatrix eI eJ) := by
      simp [hsub]
    _ = Matrix.det (K.reindex eI.symm eJ.symm) := by
      simp [Matrix.reindex_apply]
    _ = Equiv.Perm.sign (eJ.symm.trans eI) * Matrix.det K := by
      simpa [eI, eJ] using (Matrix.det_reindex (e := eI.symm) (e' := eJ.symm) K)
    _ = 0 := by
      simp [hdet]

open Matrix in
open Polynomial in
theorem RS_exists_nonzero_kernelVec_of_det_eq_zero {F : Type} [Field F] (e : ℕ)
    (K : Matrix (Fin (e + 1)) (Fin (e + 1)) (Polynomial F))
    (hdet : Matrix.det K = 0) :
    ∃ a : Fin (e + 1) → (Polynomial F), a ≠ 0 ∧ Matrix.mulVec K a = 0 := by
  classical
  rcases (Matrix.exists_mulVec_eq_zero_iff (M := K)).2 hdet with ⟨a, ha0, hmul⟩
  refine ⟨a, ha0, ?_⟩
  simpa using hmul

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
    Nat.floor (δ * Fintype.card ι) + 1 ≤ Fintype.card ι := by
  classical
  -- abbreviate the main numerals
  set n : ℕ := Fintype.card ι
  set e : ℕ := Nat.floor (δ * n)
  have heBW : 2 * e < n - deg + 1 := by
    simpa [n, e] using (RS_BW_bound_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hdeg hδ)
  have hdegpos : 0 < deg := Nat.pos_of_ne_zero (NeZero.ne deg)
  have hdeg1 : 1 ≤ deg := Nat.succ_le_iff.2 hdegpos
  have hle : n - deg + 1 ≤ n := by
    calc
      n - deg + 1 ≤ n - deg + deg := by
        exact Nat.add_le_add_left hdeg1 (n - deg)
      _ = n := by
        exact Nat.sub_add_cancel (by simpa [n] using hdeg)
  have h2 : 2 * e < n := lt_of_lt_of_le heBW hle
  have hele : e ≤ 2 * e := by
    simp [two_mul]
  have hlt : e < n := lt_of_le_of_lt hele h2
  -- finish
  simpa [n, e, Nat.succ_eq_add_one] using (Nat.succ_le_of_lt hlt)

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
      simp [Matrix.vandermonde]
    -- Map the determinant through `Polynomial.C` and rewrite the mapped matrix as a Vandermonde.
    simpa [hvand] using
      (RingHom.map_det (f := (Polynomial.C : F →+* F[X])) (M := Matrix.vandermonde v)).symm
  -- Over a field, the Vandermonde determinant is nonzero iff the entries are distinct.
  have hne : (Matrix.vandermonde v).det ≠ 0 :=
    (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  -- In a field, nonzero elements are units.
  have hunit : IsUnit ((Matrix.vandermonde v).det) := (isUnit_iff_ne_zero).2 hne
  -- Constant polynomials are units iff their coefficients are units.
  have hunitC : IsUnit ((Polynomial.C : F →+* F[X]) ((Matrix.vandermonde v).det)) :=
    (Polynomial.isUnit_C (x := (Matrix.vandermonde v).det)).2 hunit
  -- Conclude by rewriting the determinant as a constant polynomial.
  simpa [hdet] using hunitC

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
    Matrix.mulVec A (fun k : Fin n => A.adjugate k j) i = (A * A.adjugate) i j := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    _ = (A.det • (1 : Matrix (Fin n) (Fin n) (Polynomial F))) i j := by
      simpa using
        congrArg (fun M : Matrix (Fin n) (Fin n) (Polynomial F) => M i j) (Matrix.mul_adjugate A)
    _ = (if i = j then Matrix.det A else 0) := by
      simp [Matrix.one_apply]

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
  classical
  -- check names
  have _ := (dotProduct : (Fin (m + n) → R) → (Fin (m + n) → R) → R)
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_add, Fin.append, Matrix.submatrix]

open Polynomial in
open Matrix in
omit [Fintype F] [DecidableEq F] in
theorem RS_natDegree_det_le_of_entry_natDegree_le_one (n : ℕ) (A : Matrix (Fin n) (Fin n) F[X])
    (hdeg : ∀ i j, (A i j).natDegree ≤ 1) :
    (Matrix.det A).natDegree ≤ n := by
  classical
  rw [Matrix.det_apply]
  -- bound degree of the determinant by bounding each Leibniz summand
  refine Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (f := fun σ : Equiv.Perm (Fin n) => (Equiv.Perm.sign σ : Units ℤ) • (∏ i : Fin n, A (σ i) i)) ?_
  intro σ hσ
  -- ignore the scalar `sign σ` (it is ±1)
  have hsign :
      ((Equiv.Perm.sign σ : Units ℤ) • (∏ i : Fin n, A (σ i) i)).natDegree
        ≤ (∏ i : Fin n, A (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simp [hs]
    · simp [hs]
  -- bound the product by summing the bounds on the factors
  have hprod : (∏ i : Fin n, A (σ i) i).natDegree ≤ n := by
    have h1 : (∏ i : Fin n, A (σ i) i).natDegree ≤ ∑ i : Fin n, (A (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => A (σ i) i))
    have h2 : (∑ i : Fin n, (A (σ i) i).natDegree) ≤ n := by
      -- each summand is ≤ 1 by hypothesis
      have hle1 : ∀ i : Fin n, (A (σ i) i).natDegree ≤ 1 := by
        intro i
        simpa using hdeg (σ i) i
      -- sum of `n` terms each ≤ 1
      have hsum' : (∑ i ∈ (Finset.univ : Finset (Fin n)), (A (σ i) i).natDegree)
          ≤ (Finset.univ : Finset (Fin n)).card • (1 : ℕ) := by
        refine Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => (A (σ i) i).natDegree) (n := (1 : ℕ)) ?_
        intro i hi
        simpa using hle1 i
      -- rewrite sums/cards
      simpa [Finset.card_univ, Fintype.card_fin] using hsum'
    exact le_trans h1 h2
  exact le_trans hsign hprod

open scoped BigOperators in
open Polynomial in
open Matrix in
omit [Fintype F] [DecidableEq F] in
theorem RS_natDegree_inv_neg_vandermonde_C_eq_zero (n : ℕ) (v : Fin n → F)
    (hv : Function.Injective v) :
    ∀ i j : Fin n,
      ((-Matrix.vandermonde (fun t : Fin n => (Polynomial.C (v t) : F[X])))⁻¹ i j).natDegree =
        0 :=
    by
  classical
  intro i j
  let f : F →+* F[X] := Polynomial.C
  let D0 : Matrix (Fin n) (Fin n) F := -Matrix.vandermonde v
  let D : Matrix (Fin n) (Fin n) F[X] :=
    -Matrix.vandermonde (fun t : Fin n => (Polynomial.C (v t) : F[X]))
  change ((D⁻¹ i j).natDegree = 0)
  have hDmap : D = D0.map f := by
    ext i j
    simp [D, D0, Matrix.vandermonde, Matrix.map_apply, f, map_pow]
  have hdetV : (Matrix.det (Matrix.vandermonde v)) ≠ 0 := by
    simpa using (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  have hdetD0 : (Matrix.det D0) ≠ 0 := by
    have h : ((-1 : F) ^ (Fintype.card (Fin n)) * Matrix.det (Matrix.vandermonde v)) ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ (by simp)) hdetV
    simpa [D0, Matrix.det_neg] using h
  have hunit0 : IsUnit (Matrix.det D0) := (isUnit_iff_ne_zero).2 hdetD0
  have hmul0 : D0 * D0⁻¹ = 1 := Matrix.mul_nonsing_inv D0 hunit0
  have hmul : (D0.map f) * ((D0⁻¹).map f) = (1 : Matrix (Fin n) (Fin n) F[X]) := by
    simpa [Matrix.map_mul] using congrArg (fun A : Matrix (Fin n) (Fin n) F => A.map f) hmul0
  have hmul' : D * ((D0⁻¹).map f) = (1 : Matrix (Fin n) (Fin n) F[X]) := by
    simpa [hDmap] using hmul
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
  have hdet : V.det ≠ 0 := by
    simpa [V] using (Matrix.det_vandermonde_ne_zero_iff (v := v)).2 hv
  have hmul : V *ᵥ b = 0 := by
    funext j
    have hj := h (r0 j)
    -- Expand the matrix-vector product.
    -- `mulVec` uses `∑ s, V j s * b s` while our hypothesis has `b s * ...`.
    -- Commutativity of multiplication in `F[X]` reconciles the order.
    simpa [Matrix.mulVec, dotProduct, V, v, mul_comm, mul_left_comm, mul_assoc] using hj
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
    have hi := (hEq i).symm
    simpa [ha0] using hi
  have hb0 : b = 0 :=
    RS_vandermonde_coeffs_eq_zero (ι := ι) (F := F) (m := e + deg) (domain := domain) hdeg b hVand
  have happend0 : Fin.append a b = 0 := by
    ext i
    cases i using Fin.addCases <;> simp [ha0, hb0]
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
omit [Fintype F] [DecidableEq F] in
theorem RS_exists_nonzero_kernelVec_of_det_eq_zero_natDegree_le_one (e : ℕ)
    (K : Matrix (Fin (e + 1)) (Fin (e + 1)) F[X])
    (hdeg : ∀ i j, (K i j).natDegree ≤ 1)
    (hdet : Matrix.det K = 0) :
    ∃ a : Fin (e + 1) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧ Matrix.mulVec K a = 0 := by
  classical
  let n : ℕ := e + 1
  let P : ℕ → Prop := fun r =>
    ∃ (I J : Fin r ↪ Fin n), Matrix.det (K.submatrix I J) ≠ 0
  have hP0 : P 0 := by
    refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
    simp
  let r : ℕ := Nat.findGreatest P n
  have hPr : P r := by
    have h :=
      Nat.findGreatest_spec (P := P) (m := 0) (n := n) (Nat.zero_le n) hP0
    simpa [r] using h
  rcases hPr with ⟨I, J, hIJ⟩
  have hPn : ¬ P n := by
    intro h
    rcases h with ⟨I0, J0, hdet0⟩
    have hzero := RS_det_submatrix_eq_zero_of_det_eq_zero n K hdet I0 J0
    exact hdet0 hzero
  have hr_le : r ≤ n := by
    simpa [r] using (Nat.findGreatest_le (P := P) n)
  have hr_lt : r < n := by
    have hr_ne : r ≠ n := by
      intro hEq
      have : P n := by
        simpa [hEq] using (show P r from ⟨I, J, hIJ⟩)
      exact hPn this
    exact lt_of_le_of_ne hr_le hr_ne
  have hr_le_e : r ≤ e := by
    have : r < e + 1 := by
      simpa [n] using hr_lt
    exact (Nat.lt_succ_iff.mp this)
  have hnotP_succ : ¬ P (r + 1) := by
    have hr1_le : r + 1 ≤ n := Nat.succ_le_of_lt hr_lt
    have hk : Nat.findGreatest P n < r + 1 := by
      simp [r]
    exact Nat.findGreatest_is_greatest (P := P) (n := n) (k := r + 1) hk hr1_le
  have hcard_lt_I : (Finset.univ.map I).card < (Finset.univ : Finset (Fin n)).card := by
    simpa [Finset.card_map, Finset.card_univ, Fintype.card_fin] using hr_lt
  obtain ⟨i0, -, hi0_not_mem⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt_I
  have hi0 : i0 ∉ Set.range I := by
    intro hi
    rcases hi with ⟨t, rfl⟩
    have : (I t) ∈ (Finset.univ.map I) := by
      simp
    exact hi0_not_mem this
  have hcard_lt_J : (Finset.univ.map J).card < (Finset.univ : Finset (Fin n)).card := by
    simpa [Finset.card_map, Finset.card_univ, Fintype.card_fin] using hr_lt
  obtain ⟨j0, -, hj0_not_mem⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt_J
  have hj0 : j0 ∉ Set.range J := by
    intro hj
    rcases hj with ⟨t, rfl⟩
    have : (J t) ∈ (Finset.univ.map J) := by
      simp
    exact hj0_not_mem this
  let I' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc I hi0
  let J' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc J hj0
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := K.submatrix I' J'
  have hdetB : Matrix.det B = 0 := by
    by_contra h
    exact hnotP_succ ⟨I', J', h⟩
  let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)
  have hBu : Matrix.mulVec B u = 0 := by
    simpa [u] using
      (RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB)
  have hu_last : u (Fin.last r) ≠ 0 := by
    have hAdj := RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)
    have hBsub : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
      ext i j
      simp [B, I', J']
    have hUL :
        u (Fin.last r) =
          (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) * Matrix.det (K.submatrix I J) := by
      dsimp [u]
      rw [hAdj]
      simp [hBsub]
    have hsign :
        ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) ≠ 0 := by
      have hbase : (-1 : F[X]) ≠ 0 := by
        simp
      exact pow_ne_zero _ hbase
    rw [hUL]
    exact mul_ne_zero hsign hIJ
  have hu_ne : u ≠ 0 := by
    intro hu0
    have h := congrArg (fun f => f (Fin.last r)) hu0
    have : u (Fin.last r) = 0 := by
      simpa using h
    exact hu_last this
  have hu_deg : ∀ t, (u t).natDegree ≤ e := by
    intro t
    have hAdj :
        u t =
          (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
            Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
      dsimp [u]
      exact RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)
    let M : Matrix (Fin r) (Fin r) F[X] := B.submatrix Fin.castSucc t.succAbove
    have hdegM : ∀ i j, (M i j).natDegree ≤ 1 := by
      intro i j
      dsimp [M, B]
      exact hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))
    have hdetMdeg : (Matrix.det M).natDegree ≤ r :=
      RS_natDegree_det_le_of_entry_natDegree_le_one r M hdegM
    have hmuldeg : (u t).natDegree ≤ (Matrix.det M).natDegree := by
      rw [hAdj]
      dsimp [M]
      have hconst :
          (-1 : F[X]) ^ (r + (t : ℕ)) = Polynomial.C ((-1 : F) ^ (r + (t : ℕ))) := by
        simp
      rw [hconst]
      exact Polynomial.natDegree_C_mul_le _ _
    have : (u t).natDegree ≤ r := le_trans hmuldeg hdetMdeg
    exact le_trans this hr_le_e
  let a : Fin n → F[X] := Function.extend (J' : Fin (r + 1) → Fin n) u (fun _ => 0)
  have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := by
    intro t
    simpa [a] using (J'.injective.extend_apply u (fun _ => 0) t)
  have ha_ne : a ≠ 0 := by
    intro ha0
    have h := congrArg (fun f => f (J' (Fin.last r))) ha0
    have ha_last : a (J' (Fin.last r)) = 0 := by
      simpa using h
    have : u (Fin.last r) = 0 := by
      calc
        u (Fin.last r) = a (J' (Fin.last r)) := by
          symm
          exact ha_on (Fin.last r)
        _ = 0 := ha_last
    exact hu_last this
  have ha_deg : ∀ t, (a t).natDegree ≤ e := by
    intro t
    by_cases ht : ∃ s : Fin (r + 1), (J' s : Fin n) = t
    · rcases ht with ⟨s, rfl⟩
      simpa [ha_on s] using hu_deg s
    · have : a t = 0 := by
        simpa [a] using
          (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
            (b := t) ht)
      simp [this]
  have hmulVec_eq (i : Fin n) :
      (Matrix.mulVec K a) i = ∑ j : Fin (r + 1), K i (J' j) * u j := by
    classical
    have houtside :
        ∀ j : Fin n,
          j ∉ Set.range (J' : Fin (r + 1) → Fin n) → K i j * a j = 0 := by
      intro j hj
      have hj' : ¬ ∃ t : Fin (r + 1), (J' t : Fin n) = j := hj
      have ha0 : a j = 0 := by
        simpa [a] using
          (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
            (b := j) hj')
      simp [ha0]
    have hsum :
        (∑ j : Fin n, K i j * a j) = ∑ t : Fin (r + 1), K i (J' t) * a (J' t) := by
      have h :=
        (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin n)) (he := J'.injective)
          (f := fun t : Fin (r + 1) => K i (J' t) * a (J' t))
          (g := fun j : Fin n => K i j * a j) (h' := houtside) (h := fun t => rfl))
      exact h.symm
    calc
      (Matrix.mulVec K a) i = ∑ j : Fin n, K i j * a j := by
        rfl
      _ = ∑ t : Fin (r + 1), K i (J' t) * a (J' t) := hsum
      _ = ∑ t : Fin (r + 1), K i (J' t) * u t := by
        refine Fintype.sum_congr _ _ ?_
        intro t
        rw [ha_on t]
  have hKa : Matrix.mulVec K a = 0 := by
    funext i
    have hrewrite := hmulVec_eq i
    by_cases hi : i ∈ Set.range I
    · rcases hi with ⟨t, rfl⟩
      have hBu_t : (Matrix.mulVec B u) (Fin.castSucc t) = 0 := by
        have := congrArg (fun f => f (Fin.castSucc t)) hBu
        simpa using this
      have hBsum :
          (Matrix.mulVec B u) (Fin.castSucc t) = ∑ j : Fin (r + 1), K (I t) (J' j) * u j := by
        simp [B, I', Matrix.mulVec, dotProduct]
      have hsum0 : (∑ j : Fin (r + 1), K (I t) (J' j) * u j) = 0 := by
        simpa [hBsum] using hBu_t
      exact hrewrite.trans hsum0
    · have hi' : i ∉ Set.range I := hi
      let Ii : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc I hi'
      let b : Fin (r + 1) → F[X] := fun j => K i (J' j)
      have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
        ext irow jcol
        cases irow using Fin.lastCases with
        | last =>
            simp [B, I', Ii, b, Matrix.updateRow]
        | cast t =>
            simp [B, I', Ii, b, Matrix.updateRow]
      have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
        by_contra h
        exact hnotP_succ ⟨Ii, J', h⟩
      have hdetUpdate : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
        simpa [hupdate] using hdetBi
      have hsum_eq_det :
          (∑ j : Fin (r + 1), K i (J' j) * u j) = Matrix.det (B.updateRow (Fin.last r) b) := by
        simpa [b, u] using
          (det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)).symm
      have hsum0 : (∑ j : Fin (r + 1), K i (J' j) * u j) = 0 := by
        simpa [hsum_eq_det] using hdetUpdate
      exact hrewrite.trans hsum0
  refine ⟨a, ha_ne, ha_deg, ?_⟩
  simpa [a, n] using hKa

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
  letI : DecidablePred P := Classical.decPred _
  have P0 : P 0 := by
    refine ⟨Function.Embedding.ofIsEmpty, Function.Embedding.ofIsEmpty, ?_⟩
    simp
  let r : ℕ := Nat.findGreatest P n
  have Pr : P r := by
    simpa [r] using
      (Nat.findGreatest_spec (P := P) (n := n) (m := 0) (Nat.zero_le n) P0)
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
      simpa [A] using hdet_sub
    exact hdet0 hdetK
  have hrle : r ≤ n := by
    simpa [r] using (Nat.findGreatest_le (P := P) n)
  have hrne : r ≠ n := by
    intro hre
    have hEq : Nat.findGreatest P n = n := by
      simpa [r] using hre
    have hcond : n ≠ 0 → P n :=
      (Nat.findGreatest_eq_iff (P := P) (k := n) (m := n)).1 hEq |>.2.1
    have hn0 : n ≠ 0 := by
      simp [n]
    exact hnotPn (hcond hn0)
  have hrlt : r < n := Nat.lt_of_le_of_ne hrle hrne
  have hrle_e : r ≤ e := by
    have : r < e + 1 := by
      simpa [n] using hrlt
    exact Nat.lt_succ_iff.mp this
  have hcard' : n ≤ Fintype.card ι := by
    simpa [n] using hcard
  have hrltcardι : r < Fintype.card ι := lt_of_lt_of_le hrlt hcard'
  -- pick i0 ∉ range I
  let sI : Finset ι := Finset.univ.map I
  have hsIlt : sI.card < (Finset.univ : Finset ι).card := by
    simpa [sI] using hrltcardι
  obtain ⟨i0, -, hi0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsIlt
  have hi0 : i0 ∉ Set.range I := by
    intro hi
    rcases hi with ⟨i, rfl⟩
    apply hi0_notmem
    refine Finset.mem_map.2 ?_
    refine ⟨i, by simp, rfl⟩
  -- pick j0 ∉ range J
  let sJ : Finset (Fin n) := Finset.univ.map J
  have hsJlt : sJ.card < (Finset.univ : Finset (Fin n)).card := by
    simpa [sJ] using hrlt
  obtain ⟨j0, -, hj0_notmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hsJlt
  have hj0 : j0 ∉ Set.range J := by
    intro hj
    rcases hj with ⟨j, rfl⟩
    apply hj0_notmem
    refine Finset.mem_map.2 ?_
    refine ⟨j, by simp, rfl⟩
  let I' : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi0
  let J' : Fin (r + 1) ↪ Fin n := Fin.Embedding.snoc J hj0
  let B : Matrix (Fin (r + 1)) (Fin (r + 1)) F[X] := K.submatrix I' J'
  have hnotPr1 : ¬ P (r + 1) := by
    have hk : Nat.findGreatest P n < r + 1 := by
      simp [r]
    have hkb : r + 1 ≤ n := Nat.succ_le_of_lt hrlt
    exact Nat.findGreatest_is_greatest (P := P) (n := n) (k := r + 1) hk hkb
  have hdetB : Matrix.det B = 0 := by
    by_contra hne
    have : P (r + 1) := ⟨I', J', by simpa [B] using hne⟩
    exact hnotPr1 this
  let u : Fin (r + 1) → F[X] := fun t => B.adjugate t (Fin.last r)
  have hBu : Matrix.mulVec B u = 0 := by
    simpa [u] using
      RS_mulVec_adjugate_col_eq_zero_of_det_eq_zero (n := r + 1) (A := B) (j := Fin.last r) hdetB
  have hsub_cast : B.submatrix Fin.castSucc Fin.castSucc = K.submatrix I J := by
    funext i
    funext j
    simp [B, I', J']
  have hu_last : u (Fin.last r) =
      (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) *
        Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) := by
    simpa [u] using RS_adjugate_last_last_eq_det_submatrix_castSucc_castSucc (n := r) (B := B)
  have hu_last_ne : u (Fin.last r) ≠ (0 : F[X]) := by
    have hsign : (-1 : F[X]) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) ≠ (0 : F[X]) := by
      have hminus1 : (-1 : F[X]) ≠ (0 : F[X]) := by simp
      exact pow_ne_zero _ hminus1
    have hdetMinor : Matrix.det (B.submatrix Fin.castSucc Fin.castSucc) ≠ (0 : F[X]) := by
      simpa [hsub_cast] using hdetIJ
    rw [hu_last]
    exact mul_ne_zero hsign hdetMinor
  -- degree bound on u
  have hdeg_u : ∀ t : Fin (r + 1), (u t).natDegree ≤ r := by
    intro t
    have hu_t : u t =
        (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)) *
          Matrix.det (B.submatrix Fin.castSucc t.succAbove) := by
      simpa [u] using RS_adjugate_fin_succ_eq_det_submatrix_last_castSucc (n := r) (B := B) (t := t)
    have hdeg_det : (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ r := by
      apply RS_natDegree_det_le_of_entry_natDegree_le_one (n := r)
        (A := B.submatrix Fin.castSucc t.succAbove)
      intro i j
      -- entries come from K
      simpa [B] using hdeg (I' (Fin.castSucc i)) (J' (t.succAbove j))
    have hdeg_sign : ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree = 0 := by
      simp
    have hmul_le :
        (u t).natDegree ≤
          ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
            (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree := by
      simpa [hu_t] using
        (Polynomial.natDegree_mul_le
          (p := (-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ)))
          (q := Matrix.det (B.submatrix Fin.castSucc t.succAbove)))
    have hdeg_rhs :
        ((-1 : F[X]) ^ ((Fin.last r : ℕ) + (t : ℕ))).natDegree +
            (Matrix.det (B.submatrix Fin.castSucc t.succAbove)).natDegree ≤ r := by
      simpa [hdeg_sign] using hdeg_det
    exact le_trans hmul_le hdeg_rhs
  -- extend u to all columns
  let a : Fin n → F[X] := Function.extend (J' : Fin (r + 1) → Fin n) u (fun _ => 0)
  have ha_on : ∀ t : Fin (r + 1), a (J' t) = u t := by
    intro t
    simpa [a] using (J'.injective.extend_apply u (fun _ => 0) t)
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hval : a (J' (Fin.last r)) = 0 := by
      simpa using congrArg (fun f : Fin n → F[X] => f (J' (Fin.last r))) ha0
    have : u (Fin.last r) = 0 := by
      simpa [ha_on (Fin.last r)] using hval
    exact hu_last_ne this
  have hdeg_a : ∀ j : Fin n, (a j).natDegree ≤ e := by
    intro j
    by_cases hj : ∃ t : Fin (r + 1), J' t = j
    · rcases hj with ⟨t, rfl⟩
      exact le_trans (by simpa [ha_on t] using hdeg_u t) hrle_e
    · have haj : a j = 0 := by
        simpa [a] using
          (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
            (b := j) hj)
      simp [haj]
  have hmul_formula (i : ι) : Matrix.mulVec K a i = ∑ t : Fin (r + 1), K i (J' t) * u t := by
    have hsum : (∑ t : Fin (r + 1), K i (J' t) * u t) = ∑ j : Fin n, K i j * a j := by
      refine (Fintype.sum_of_injective (e := (J' : Fin (r + 1) → Fin n)) (he := J'.injective)
        (f := fun t : Fin (r + 1) => K i (J' t) * u t)
        (g := fun j : Fin n => K i j * a j) ?_ ?_)
      · intro j hj
        have hb : ¬∃ t : Fin (r + 1), (J' t) = j := by
          simpa [Set.mem_range] using hj
        have haj : a j = 0 := by
          simpa [a] using
            (Function.extend_apply' (f := (J' : Fin (r + 1) → Fin n)) (g := u) (e' := fun _ => 0)
              (b := j) hb)
        simp [haj]
      · intro t
        simp [ha_on t]
    simpa [Matrix.mulVec] using hsum.symm
  have hmulVec : Matrix.mulVec K a = 0 := by
    funext i
    by_cases hi : i ∈ Set.range I
    · rcases hi with ⟨t, rfl⟩
      have hrow : (Matrix.mulVec B u) (Fin.castSucc t) = 0 := by
        have := congrArg (fun v : Fin (r + 1) → F[X] => v (Fin.castSucc t)) hBu
        simpa using this
      have hrow' : (∑ x : Fin (r + 1), K (I t) (J' x) * u x) = 0 := by
        simpa [Matrix.mulVec, B, I', J'] using hrow
      rw [hmul_formula (i := I t)]
      simpa using hrow'
    · -- i ∉ range I
      have hi' : i ∉ Set.range I := hi
      let Ii : Fin (r + 1) ↪ ι := Fin.Embedding.snoc I hi'
      have hdetBi : Matrix.det (K.submatrix Ii J') = 0 := by
        by_contra hne
        have : P (r + 1) := ⟨Ii, J', by simpa using hne⟩
        exact hnotPr1 this
      let b : Fin (r + 1) → F[X] := fun j => K i (J' j)
      have hupdate : B.updateRow (Fin.last r) b = K.submatrix Ii J' := by
        funext x
        funext y
        refine Fin.lastCases (motive := fun x => (B.updateRow (Fin.last r) b) x y =
            (K.submatrix Ii J') x y) ?_ ?_ x
        · -- x = last
          simp [Matrix.updateRow_apply, b, B, Ii, I', J']
        · intro x
          simp [Matrix.updateRow_apply, b, B, Ii, I', J']
      have hdet_update : Matrix.det (B.updateRow (Fin.last r) b) = 0 := by
        simpa [hupdate] using hdetBi
      have hdet_expr : Matrix.det (B.updateRow (Fin.last r) b) =
          ∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r) := by
        simpa using
          det_updateRow_eq_sum_mul_adjugate_col (A := B) (i := Fin.last r) (b := b)
      have hsum0 : (∑ j : Fin (r + 1), b j * B.adjugate j (Fin.last r)) = 0 := by
        simpa [hdet_expr] using hdet_update
      have hsum0' : (∑ j : Fin (r + 1), K i (J' j) * u j) = 0 := by
        simpa [b, u] using hsum0
      rw [hmul_formula (i := i)]
      simpa using hsum0'
  refine ⟨a, ha_ne, ?_, hmulVec⟩
  intro t
  simpa using hdeg_a t

end CoreResults

end ProximityGap

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.SeparableResultant

/-!
# Sharp coefficient degrees for derivative resultants

For a polynomial `A(Y) = ∑ᵢ aᵢ(X)Yⁱ` of total degree at most `j`, the padded
Sylvester determinant for `A` and `A'` remembers the coefficient indices.  Every determinant
term contains `b - 1` coefficients of `A` and `b` coefficients of `A'`; the sum of their
indices is `b(b-1)`, and differentiation contributes one further unit in each of the `b`
derivative columns.  This gives the sharp bound

`deg_X Res(A', A) ≤ (2b-1)j-b²`.

The Sylvester sizes remain the declared original sizes under every coefficient specialization.
The final common-root lemma therefore also covers specializations at which either actual degree
drops.
-/

@[expose] public section

namespace Polynomial

open scoped BigOperators

variable {R S : Type*} [CommRing R]

/-- The sharp total-degree bound for the derivative resultant, written without truncated
subtraction.  The coefficient premise is the homogeneous-triangle condition
`i + deg_X(aᵢ) ≤ j`; exact outer degree supplies `b ≤ j` and handles zero determinant terms. -/
theorem natDegree_separableResultant_add_sq_le_of_le
    (A : R[X][X]) {b j : ℕ} (hb : 0 < b) (_hdegree : A.natDegree = b)
    (hcoeff : ∀ i, i ≤ b → i + (A.coeff i).natDegree ≤ j) :
    (separableResultant A b).natDegree + b ^ 2 ≤ (2 * b - 1) * j := by
  classical
  have hbj : b ≤ j := (Nat.le_add_right b _).trans (hcoeff b le_rfl)
  have hsq : b ^ 2 ≤ (2 * b - 1) * j := by
    calc
      b ^ 2 = b * b := by simp [pow_two]
      _ ≤ b * j := Nat.mul_le_mul_left b hbj
      _ ≤ (2 * b - 1) * j := Nat.mul_le_mul_right j (by omega)
  let m := b - 1
  let M : Matrix (Fin (m + b)) (Fin (m + b)) R[X] :=
    sylvester A.derivative A m b
  change M.det.natDegree + b ^ 2 ≤ (2 * b - 1) * j
  rw [← Nat.le_sub_iff_add_le hsq]
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_smul_le _ _).trans ?_
  by_cases hzero : ∃ i : Fin (m + b), M (σ i) i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hprod : (∏ i : Fin (m + b), M (σ i) i) = 0 :=
      Finset.prod_eq_zero (s := Finset.univ) (Finset.mem_univ i) hi
    rw [hprod]
    simp
  · have hne (i : Fin (m + b)) : M (σ i) i ≠ 0 := by
      intro hi
      exact hzero ⟨i, hi⟩
    let lidx : Fin m → ℕ := fun c =>
      ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) - (c : ℕ)
    let ridx : Fin b → ℕ := fun c =>
      ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) - (c : ℕ)
    let ldeg : Fin m → ℕ := fun c =>
      (M (σ (Fin.castAdd b c)) (Fin.castAdd b c)).natDegree
    let rdeg : Fin b → ℕ := fun c =>
      (M (σ (Fin.natAdd m c)) (Fin.natAdd m c)).natDegree
    have hleft_Icc (c : Fin m) :
        ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) ∈
          Set.Icc (c : ℕ) ((c : ℕ) + b) := by
      have hentry : M (σ (Fin.castAdd b c)) (Fin.castAdd b c) =
          if ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) ∈
              Set.Icc (c : ℕ) ((c : ℕ) + b) then
            A.coeff (((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) - (c : ℕ))
          else 0 := by
        simp [M, sylvester]
      by_contra hc
      have hz : M (σ (Fin.castAdd b c)) (Fin.castAdd b c) = 0 := by
        rw [hentry, if_neg hc]
      exact hne (Fin.castAdd b c) hz
    have hright_Icc (c : Fin b) :
        ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) ∈
          Set.Icc (c : ℕ) ((c : ℕ) + m) := by
      have hentry : M (σ (Fin.natAdd m c)) (Fin.natAdd m c) =
          if ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) ∈
              Set.Icc (c : ℕ) ((c : ℕ) + m) then
            A.derivative.coeff
              (((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) - (c : ℕ))
          else 0 := by
        simp [M, sylvester]
      by_contra hc
      have hz : M (σ (Fin.natAdd m c)) (Fin.natAdd m c) = 0 := by
        rw [hentry, if_neg hc]
      exact hne (Fin.natAdd m c) hz
    have hleft (c : Fin m) : lidx c + ldeg c ≤ j := by
      dsimp [lidx, ldeg]
      have hc := hleft_Icc c
      have hcLower : (c : ℕ) ≤ ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) := hc.1
      have hcUpper : ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) ≤ (c : ℕ) + b := hc.2
      have hidx :
          ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) - (c : ℕ) ≤ b := by
        omega
      have hentry :
          M (σ (Fin.castAdd b c)) (Fin.castAdd b c) =
            if ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) ∈
                Set.Icc (c : ℕ) ((c : ℕ) + b) then
              A.coeff (((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) - (c : ℕ))
            else 0 := by
        simp [M, sylvester]
      rw [hentry, if_pos hc]
      exact hcoeff _ hidx
    have hright (c : Fin b) : ridx c + 1 + rdeg c ≤ j := by
      dsimp [ridx, rdeg]
      have hc := hright_Icc c
      have hcLower : (c : ℕ) ≤ ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) := hc.1
      have hcUpper : ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) ≤ (c : ℕ) + m := hc.2
      have hidx :
          ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) - (c : ℕ) + 1 ≤ b := by
        dsimp only [m] at hcUpper ⊢
        omega
      have hentry :
          M (σ (Fin.natAdd m c)) (Fin.natAdd m c) =
            if ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) ∈
                Set.Icc (c : ℕ) ((c : ℕ) + m) then
              A.derivative.coeff
                (((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) - (c : ℕ))
            else 0 := by
        simp [M, sylvester]
      rw [hentry, if_pos hc]
      have hd := coeff_derivative_natDegree_le A
        (((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) - (c : ℕ))
      have hs := hcoeff
        ((((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) - (c : ℕ)) + 1) hidx
      omega
    have hleft_sum :
        (∑ c : Fin m, (lidx c + ldeg c)) ≤ m * j := by
      calc
        (∑ c : Fin m, (lidx c + ldeg c)) ≤ ∑ _c : Fin m, j :=
          Finset.sum_le_sum fun c _ => hleft c
        _ = m * j := by simp
    have hright_sum :
        (∑ c : Fin b, (ridx c + 1 + rdeg c)) ≤ b * j := by
      calc
        (∑ c : Fin b, (ridx c + 1 + rdeg c)) ≤ ∑ _c : Fin b, j :=
          Finset.sum_le_sum fun c _ => hright c
        _ = b * j := by simp
    have hidxsum :
        (∑ c : Fin m, lidx c) + (∑ c : Fin b, ridx c) = b * m := by
      have hleft_row (c : Fin m) :
          ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ) = (c : ℕ) + lidx c := by
        dsimp [lidx]
        have hle := (Set.mem_Icc.mp (hleft_Icc c)).1
        omega
      have hright_row (c : Fin b) :
          ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) = (c : ℕ) + ridx c := by
        dsimp [ridx]
        have hle := (Set.mem_Icc.mp (hright_Icc c)).1
        omega
      have hperm :
          (∑ i : Fin (m + b), ((σ i : Fin (m + b)) : ℕ)) =
            ∑ i : Fin (m + b), (i : ℕ) := by
        simpa using Equiv.sum_comp σ (fun i : Fin (m + b) => (i : ℕ))
      have hrows :
          (∑ i : Fin (m + b), ((σ i : Fin (m + b)) : ℕ)) =
            (∑ c : Fin m, ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ)) +
              ∑ c : Fin b, ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ) := by
        simpa using Fin.sum_univ_add
          (fun i : Fin (m + b) => ((σ i : Fin (m + b)) : ℕ))
      have hcols :
          (∑ i : Fin (m + b), (i : ℕ)) =
            (∑ c : Fin m, (c : ℕ)) + ∑ c : Fin b, (m + (c : ℕ)) := by
        simpa using Fin.sum_univ_add (fun i : Fin (m + b) => (i : ℕ))
      have hsum_left_rows :
          (∑ c : Fin m, ((σ (Fin.castAdd b c) : Fin (m + b)) : ℕ)) =
            (∑ c : Fin m, (c : ℕ)) + ∑ c : Fin m, lidx c := by
        calc
          _ = ∑ c : Fin m, ((c : ℕ) + lidx c) := by
            exact Finset.sum_congr rfl fun c _ => hleft_row c
          _ = _ := Finset.sum_add_distrib
      have hsum_right_rows :
          (∑ c : Fin b, ((σ (Fin.natAdd m c) : Fin (m + b)) : ℕ)) =
            (∑ c : Fin b, (c : ℕ)) + ∑ c : Fin b, ridx c := by
        calc
          _ = ∑ c : Fin b, ((c : ℕ) + ridx c) := by
            exact Finset.sum_congr rfl fun c _ => hright_row c
          _ = _ := Finset.sum_add_distrib
      have hright_cols :
          (∑ c : Fin b, (m + (c : ℕ))) = b * m + ∑ c : Fin b, (c : ℕ) := by
        simp [Finset.sum_add_distrib, Finset.sum_const]
      rw [hrows, hsum_left_rows, hsum_right_rows] at hperm
      rw [hcols, hright_cols] at hperm
      omega
    have hdeg :
        (∑ c : Fin m, ldeg c) + (∑ c : Fin b, rdeg c) + b ^ 2 ≤
          (2 * b - 1) * j := by
      have hsums := Nat.add_le_add hleft_sum hright_sum
      simp_rw [Finset.sum_add_distrib] at hsums
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.mul_one] at hsums
      have hm : m + b = 2 * b - 1 := by simp [m]; omega
      have hsq' : b * m + b = b ^ 2 := by
        calc
          b * m + b = b * (m + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = b * b := by
            rw [show m + 1 = b by
              change b - 1 + 1 = b
              exact Nat.sub_add_cancel hb]
          _ = b ^ 2 := by simp [pow_two]
      have hsums' :
          ((∑ c : Fin m, lidx c) + ∑ c : Fin b, ridx c) + b +
              ((∑ c : Fin m, ldeg c) + ∑ c : Fin b, rdeg c) ≤
            m * j + b * j := by
        calc
          _ = (∑ c : Fin m, lidx c) + (∑ c : Fin m, ldeg c) +
                ((∑ c : Fin b, ridx c) + b + ∑ c : Fin b, rdeg c) := by
            ac_rfl
          _ ≤ m * j + b * j := hsums
      rw [← Nat.add_mul] at hsums'
      rw [hidxsum, hsq', hm] at hsums'
      omega
    have hsplit :
        (∑ i : Fin (m + b), (M (σ i) i).natDegree) =
          (∑ c : Fin m, ldeg c) + ∑ c : Fin b, rdeg c := by
      simpa only [ldeg, rdeg] using
        Fin.sum_univ_add (fun i : Fin (m + b) => (M (σ i) i).natDegree)
    apply Nat.le_sub_of_add_le
    calc
      (∏ i : Fin (m + b), M (σ i) i).natDegree + b ^ 2 ≤
          (∑ i : Fin (m + b), (M (σ i) i).natDegree) + b ^ 2 :=
        Nat.add_le_add_right (natDegree_prod_le Finset.univ _) _
      _ = ((∑ c : Fin m, ldeg c) + ∑ c : Fin b, rdeg c) + b ^ 2 := by
        rw [hsplit]
      _ ≤ (2 * b - 1) * j := hdeg

/-- Compatibility form with the coefficient triangle stated at every natural index. -/
theorem natDegree_separableResultant_add_sq_le
    (A : R[X][X]) {b j : ℕ} (hb : 0 < b) (hdegree : A.natDegree = b)
    (hcoeff : ∀ i, i + (A.coeff i).natDegree ≤ j) :
    (separableResultant A b).natDegree + b ^ 2 ≤ (2 * b - 1) * j := by
  exact natDegree_separableResultant_add_sq_le_of_le A hb hdegree
    (fun i _ ↦ hcoeff i)

/-- Sharp derivative-resultant degree with the manuscript's exact truncated subtraction. -/
theorem natDegree_separableResultant_le_totalDegree_of_le
    (A : R[X][X]) {b j : ℕ} (hb : 0 < b) (hdegree : A.natDegree = b)
    (hcoeff : ∀ i, i ≤ b → i + (A.coeff i).natDegree ≤ j) :
    (separableResultant A b).natDegree ≤ (2 * b - 1) * j - b ^ 2 := by
  apply Nat.le_sub_of_add_le
  exact natDegree_separableResultant_add_sq_le_of_le A hb hdegree hcoeff

/-- Compatibility form with the coefficient triangle stated at every natural index. -/
theorem natDegree_separableResultant_le_totalDegree
    (A : R[X][X]) {b j : ℕ} (hb : 0 < b) (hdegree : A.natDegree = b)
    (hcoeff : ∀ i, i + (A.coeff i).natDegree ≤ j) :
    (separableResultant A b).natDegree ≤ (2 * b - 1) * j - b ^ 2 := by
  exact natDegree_separableResultant_le_totalDegree_of_le A hb hdegree
    (fun i _ ↦ hcoeff i)

/-- A common root of a specialization of `A` and `A'` kills the original-size padded
Sylvester resultant.  No preservation of either specialized degree is assumed. -/
theorem separableResultant_map_eq_zero_of_common_root
    [IsDomain R] [CommRing S] [IsDomain S]
    (A : R[X][X]) {b : ℕ} (hb : 0 < b) (hdegree : A.natDegree ≤ b)
    (φ : R[X] →+* S) (u : S)
    (hroot : (A.map φ).eval u = 0)
    (hderivative : (A.map φ).derivative.eval u = 0) :
    φ (separableResultant A b) = 0 := by
  by_contra hresultant
  exact (eval_derivative_ne_zero_of_separableResultant_map_ne_zero
    A hb hdegree φ u hresultant hroot) hderivative

end Polynomial

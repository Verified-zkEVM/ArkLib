/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Rocca
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate

open Polynomial Polynomial.Bivariate Finsupp Finset

variable {F : Type} [Field F]
variable {k n m : ℕ}
variable {ωs : Fin n ↪ F}
variable {f : Fin n → F}

/-- The degree bound (i.e. `D_X(m) = (m + 1/2) * √ρ * n`) for instantiation of
    Guruswami-Sudan in Lemma 5.3 of [BCIKS20]. -/
noncomputable def proximity_gap_degree_bound (k n m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  ⌊(m + 1 / 2) * √ rho * n⌋₊

/-- The relative decoding radius (i.e. `δ₀(ρ, m) = 1 - √ρ - √ρ/2m` in
    Lemma 5.3 of [BCIKS20]). It follows from the Johnson bound. -/
noncomputable def proximity_gap_johnson (k n m : ℕ) : ℝ :=
  let rho := (k + 1 : ℚ) / n
  1 - √ rho - √ rho / (2 * m)

namespace GuruswamiSudan

/-- The monomial X^i Y^j as a bivariate polynomial. -/
noncomputable def monomial (i j : ℕ) : F[X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i 1)

section numVars

/-- Given a nonnegative integer `D`, it is the set of indices `(i,j)` such
    that `i + (k - 1) * j ≤ D`. -/
def weigthBoundIndices (k D : ℕ) : Finset (ℕ × ℕ) :=
  (range (D + 1)).product (range (D + 1)) |>.filter (fun x ↦ x.1 + (k - 1) * x.2 ≤ D)

/-- The number of variables in the Guruswami-Sudan linear system. -/
def numVars (k D : ℕ) : ℕ := (weigthBoundIndices k D).card

/-- The number of variables is the sum over j of the number of valid i's. -/
lemma card_weigthBoundIndices_eq_sum (D : ℕ) (hk : 1 < k) :
  (weigthBoundIndices k D).card = ∑ j ∈ range (D / (k - 1) + 1), (D - (k - 1) * j + 1) := by
    have h_split : (weigthBoundIndices k D).card =
        ∑ j ∈ range (D / (k - 1) + 1),
          ∑ i ∈ range (D + 1), if i + (k - 1) * j ≤ D then 1 else 0 := by
      rw [show weigthBoundIndices k D =
        filter (fun p : ℕ × ℕ ↦ p.1 + (k - 1) * p.2 ≤ D)
        ((range (D + 1)).product (range (D / (k - 1) + 1))) from ?_, card_filter]
      · erw [sum_product, Finset.sum_comm]
      · ext ⟨i, j⟩
        simp only [weigthBoundIndices, product_eq_sprod, mem_filter, mem_product, mem_range,
          and_congr_left_iff, and_congr_right_iff]
        exact fun _ _ ↦ iff_of_true (by
          nlinarith [Nat.sub_pos_of_lt hk, D.div_add_mod (k - 1),
            D.mod_lt (Nat.sub_pos_of_lt hk)])
          (Nat.lt_succ_of_le (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hk) |>.2
          (by nlinarith [Nat.sub_pos_of_lt hk])))
    have h_inner : ∀ j ∈ range (D / (k - 1) + 1), ∑ i ∈ range (D + 1),
        (if i + (k - 1) * j ≤ D then 1 else 0) = (D - (k - 1) * j) + 1 := by
      intro j hj
      have h_filter : filter (fun i ↦ i + (k - 1) * j ≤ D) (range (D + 1)) =
          Icc 0 (D - (k - 1) * j) := by
        ext i
        simp only [mem_filter, mem_range, mem_Icc, zero_le, true_and]
        refine ⟨fun h ↦ Nat.le_sub_of_add_le <| by linarith, fun h ↦ ⟨by
            nlinarith [Nat.sub_add_cancel <| show (k - 1) * j ≤ D from by
              nlinarith [Nat.sub_add_cancel <| show j ≤ D / (k - 1) from by
                linarith [mem_range.mp hj], Nat.div_mul_le_self D (k - 1)]], by
                  linarith [Nat.sub_add_cancel <| show (k - 1) * j ≤ D from by
                    nlinarith [Nat.sub_add_cancel <| show j ≤ D / (k - 1) from by
                      linarith [mem_range.mp hj], Nat.div_mul_le_self D (k - 1)]]⟩⟩
      simp_all
    exact h_split.trans (sum_congr rfl h_inner)

/-- Closed form for the number of variables when k > 1. -/
lemma numVars_eq_of_gt_one {D : ℕ} (hk : 1 < k) :
    numVars k D = let L := D / (k - 1); (L + 1) * (2 * D + 2 - (k - 1) * L) / 2 := by
      convert card_weigthBoundIndices_eq_sum D hk using 1
      have h_simp : ∑ j ∈ range (D / (k - 1) + 1), (D - (k - 1) * j) =
          (D / (k - 1) + 1) * D - (k - 1) * ((D / (k - 1)) * (D / (k - 1) + 1)) / 2 := by
        have h_simp : ∑ j ∈ range (D / (k - 1) + 1), (D - (k - 1) * j) =
            ∑ j ∈ range (D / (k - 1) + 1), D -
              ∑ j ∈ range (D / (k - 1) + 1), (k - 1) * j := by
          exact eq_tsub_of_add_eq <| by
            rw [← sum_add_distrib]
            exact sum_congr rfl fun x hx ↦ tsub_add_cancel_of_le <| by
              nlinarith [mem_range.mp hx, Nat.div_mul_le_self D (k - 1)]
        simp_all only [mul_comm, sum_const, card_range, smul_eq_mul]
        exact congrArg _ (Eq.symm <| Nat.div_eq_of_eq_mul_left zero_lt_two <| by
          rw [← sum_mul _ _ _]
          exact (D / (k - 1)).recOn (by norm_num) fun n ih ↦ by
            norm_num [range_add_one] at *; linarith)
      simp_all only [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
      rw [Nat.div_eq_of_eq_mul_left zero_lt_two]
      rw [tsub_eq_of_eq_add (c := k - 1)]
      · rw [tsub_add_eq_add_tsub]
        rotate_left
        · exact Nat.div_le_of_le_mul <| by
            nlinarith [(D / (k - 1)).zero_le, D.div_mul_le_self (k - 1),
              Nat.sub_add_cancel hk.le]
        · rw [tsub_mul, Nat.mul_sub_left_distrib]
          ring_nf
          rw [tsub_mul]
          ring_nf
          rw [Nat.div_mul_cancel]
          · rw [show D / (k - 1) * k - D / (k - 1) = D / (k - 1) * (k - 1) by
              rw [Nat.mul_sub_left_distrib, Nat.mul_one]]; ring_nf
          · norm_num [← even_iff_two_dvd, parity_simps]
      · rw [Nat.sub_add_cancel hk.le]

/-- The number of variables is (D+1)^2 when k ≤ 1. -/
lemma numVars_eq_sq {k D : ℕ} (hk : k ≤ 1) : numVars k D = (D + 1) ^ 2 := by
  interval_cases k
  all_goals
  simp only [numVars, weigthBoundIndices, tsub_self, zero_mul, add_zero, product_eq_sprod]
  norm_num
  rw [filter_true_of_mem fun x hx ↦ by linarith [mem_range.mp (mem_product.mp hx |>.1)]]
  norm_num [sq, card_product]

/-- A tighter lower bound for the number of variables when k > 1 :
    2(k-1) * numVars ≥ D(D+2). -/
lemma numVars_lower_bound_tight {D : ℕ} (hk : 1 < k) :
    2 * (k - 1) * numVars k D ≥ D * (D + 2) := by
      have h_numVars_def : numVars k D =
          ((D / (k - 1)) + 1) * (2 * D + 2 - (k - 1) * (D / (k - 1))) / 2 :=
        numVars_eq_of_gt_one hk
      rcases k with (_|_|k) <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one,
        or_true, add_tsub_cancel_right, Nat.mul_succ, ge_iff_le]
      · omega
      · omega
      rw [← Nat.mul_div_assoc]
      · rw [Nat.le_div_iff_mul_le] <;> ring_nf
        · zify
          rw [Nat.cast_sub] <;> push_cast <;>
            nlinarith [D.div_mul_le_self (1 + k), D.div_add_mod (1 + k),
              D.mod_lt (by linarith : 0 < (1 + k))]
        · norm_num
      · cases le_total (2 * D + 2) ((k + 1) * (D / (k + 1))) <;>
          simp_all [← even_iff_two_dvd, parity_simps]
        by_cases h : Even (D / (k + 1)) <;> simp_all [parity_simps]

end numVars

section numConstraints

/-- Given a positive integer `m`, the set of derivative indices `(s,t)`
    such that `s + t < m`. -/
def constraintIndices (m : ℕ) : Finset (ℕ × ℕ) :=
  (range m).product (range m) |>.filter (fun x ↦ x.1 + x.2 < m)

/-- The number of constraints in the Guruswami-Sudan linear system. -/
def numConstraints (n m : ℕ) : ℕ := n * (constraintIndices m).card

/-- The indices of constraints are `m * (m + 1) / 2`. -/
lemma card_constraintIndices (m : ℕ) : (constraintIndices m).card = m * (m + 1) / 2 := by
  rw [Nat.div_eq_of_eq_mul_left zero_lt_two]
  have h_eq : (constraintIndices m).card = ∑ s ∈ range m, (m - s) := by
    have h_sum : (constraintIndices m).card = ∑ s ∈ range m, (range (m - s)).card := by
      rw [show constraintIndices m = (range m).biUnion fun s ↦
        (range (m - s)).image (fun t ↦ (s, t))  from ?_, card_biUnion]
      · exact sum_congr rfl fun _ _ ↦
          card_image_of_injective _ fun _ _ h ↦ by exact Prod.ext_iff.mp h |>.2
      · exact fun i hi j hj hij ↦ disjoint_left.mpr fun x hx₁ hx₂ ↦ hij <| by aesop
      · ext ⟨s, t⟩
        simp [constraintIndices, mem_biUnion, mem_image]
        omega
    aesop
  exact h_eq.symm ▸ Nat.recOn m (by norm_num) fun n ih ↦ by
    cases n <;> simp [sum_range_succ', Nat.mul_succ] at *
    linarith

end numConstraints

section numVars_gt_numConstraints

/-- Lower bound for the square of (D+1). Specifically, (D+1)^2 > (m+1/2)^2 * (k+1) * n. -/
lemma proximity_gap_degree_bound_sq_gt (hn : n ≠ 0) :
    ((proximity_gap_degree_bound k n m : ℝ) + 1) ^ 2 >
      (m + 1 / 2) ^ 2 * (k + 1) * n := by
      set D := proximity_gap_degree_bound k n m
      have h_bound : (D + 1 : ℝ) > (m + 1 / 2) * √((k + 1 : ℝ) * n) := by
        have hD_ge_floor : (D : ℝ) ≥ Nat.floor ((m + 1 / 2 : ℝ) * √((k + 1 : ℝ) * n)) := by
          simp +zetaDelta only
            [ne_eq, one_div, Nat.cast_nonneg, Real.sqrt_mul', ge_iff_le, Nat.cast_le] at *
          unfold proximity_gap_degree_bound
          norm_num [mul_assoc, mul_div_assoc, hn]
          rw [mul_comm_div]
          gcongr
          field_simp
          rw [Real.sq_sqrt (by norm_cast; omega)]
        linarith [Nat.lt_floor_add_one ((m + 1 / 2 : ℝ) * √((k + 1 : ℝ) * n))]
      nlinarith [show 0 < (m + 1 / 2 : ℝ) * √((k + 1) * n) by
        positivity, Real.mul_self_sqrt (show 0 ≤ (k + 1 : ℝ) * n by positivity)]

lemma numVars_gt_numConstraints_of_gt_one (hn : n ≠ 0) (hk : 1 < k) (hm : 1 ≤ m) :
    numVars k (proximity_gap_degree_bound k n m) > numConstraints n m := by
      set D := proximity_gap_degree_bound k n m
      have hD : ((D + 1)^2 : ℝ) > ((m : ℝ) + 1 / 2)^2 * (k + 1) * n := by
        convert proximity_gap_degree_bound_sq_gt hn using 1
      have h_ineq : 2 * (k - 1) * numVars k D > (k - 1) * n * m * (m + 1) := by
        have h_ineq : 2 * (k - 1) * numVars k D ≥ (D : ℝ) * (D + 2) := by
          convert numVars_lower_bound_tight hk using 1
          · norm_cast
            rw [Int.subNatNat_of_le] <;> norm_cast
            linarith
        have h_ineq : (D : ℝ) * (D + 2) > (k - 1) * n * m * (m + 1) := by
          nlinarith [show (k : ℝ) ≥ 2 by norm_cast, show (m : ℝ) ≥ 1 by
            exact Nat.one_le_cast.mpr hm, show (n : ℝ) ≥ 1 by
              exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn), mul_le_mul_of_nonneg_left
                (show (m : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr hm)
                  (show (n : ℝ) ≥ 0 by positivity)]
        norm_cast at *
        rw [Int.subNatNat_of_le] at * <;> (norm_cast at *; linarith)
      have h_div : numVars k D > n * m * (m + 1) / 2 := by
        exact Nat.div_lt_of_lt_mul <| by nlinarith [Nat.sub_pos_of_lt hk]
      convert h_div using 1
      convert congr_arg (fun x : ℕ ↦ n * x) (card_constraintIndices m) using 1
      rw [← Nat.mul_div_assoc] <;> ring_nf
      exact even_iff_two_dvd.mp (by simp [parity_simps])

lemma numVars_gt_numConstraints (k n m : ℕ) :
  numVars k (proximity_gap_degree_bound k n m) > numConstraints n m := by
  by_cases hk : k ≤ 1
  · interval_cases k <;> norm_num [numVars_eq_sq, numConstraints]
    · unfold proximity_gap_degree_bound
      norm_num
      have h_constraint_card : (constraintIndices m).card = m * (m + 1) / 2 := by
        exact card_constraintIndices m
      rcases n with (_ | n) <;> rcases m with (_ | m) <;> norm_num at *
      · norm_num [card_constraintIndices]
      · have h_simplify : (n + 1) * (m + 1) * (m + 2) / 2 <
            (⌊((m + 1 + 1 / 2) * √(n + 1))⌋₊ + 1) ^ 2 := by
          have := Nat.lt_floor_add_one ((m + 1 + 1 / 2 : ℝ) * √(n + 1))
          rw [Nat.div_lt_iff_lt_mul <| by positivity]
          rw [← @Nat.cast_lt ℝ]
          norm_num
          ring_nf at *
          nlinarith [show 0 ≤ (m : ℝ) * √(1 + n) by
              positivity, show 0 ≤ √(1 + n) by
                  positivity, Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + n by positivity)]
        convert h_simplify using 1
        · exact (Nat.div_eq_of_eq_mul_left zero_lt_two (by
            nlinarith only [Nat.div_mul_cancel (show 2 ∣ (m + 1) * (m + 1 + 1) from
              Nat.dvd_of_mod_eq_zero <| by norm_num [Nat.add_mod, Nat.mod_two_of_bodd]),
                h_constraint_card])).symm
        · rw [mul_assoc]
          congr
          field_simp
          rw [Real.sq_sqrt (by norm_cast; omega)]
    · by_cases hn : n = 0
      · aesop
      · by_cases hm : m = 0
        · unfold constraintIndices; aesop
        · have h_ineq : (m + 1 / 2 : ℝ) ^ 2 * 2 * n > n * m * (m + 1) / 2 := by
            nlinarith [show (m : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hm),
              show (n : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn),
                mul_pos (show (m : ℝ) > 0 by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
                  (show (n : ℝ) > 0 by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
          have h_ineq : (n * m * (m + 1) / 2 : ℝ) <
              ((proximity_gap_degree_bound 1 n m + 1) : ℝ) ^ 2 := by
            refine lt_of_lt_of_le h_ineq ?_
            convert proximity_gap_degree_bound_sq_gt hn |> le_of_lt using 1
            ring
          rw [div_lt_iff₀] at h_ineq <;> norm_cast at *
          rw [card_constraintIndices]
          nlinarith [Nat.div_mul_le_self (m * (m + 1)) 2]
  · by_cases hn : n = 0 <;> by_cases hm : m = 0 <;>
      simp_all only [not_le, gt_iff_lt, numConstraints]
    · exact card_pos.mpr ⟨⟨0, 0⟩,
        mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr
          <| Nat.succ_pos _, mem_range.mpr <| Nat.succ_pos _⟩, by norm_num⟩⟩
    · norm_num
      exact card_pos.mpr ⟨⟨0, 0⟩, mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr <| Nat.succ_pos _, mem_range.mpr <| Nat.succ_pos _⟩, by norm_num⟩⟩
    · exact lt_of_lt_of_le (by simp [constraintIndices])
        (Nat.pos_of_ne_zero (ne_of_gt (card_pos.mpr ⟨(0, 0),
          mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (Nat.succ_pos _),
            mem_range.mpr (Nat.succ_pos _)⟩, by norm_num⟩⟩)))
    · exact numVars_gt_numConstraints_of_gt_one hn hk (Nat.one_le_iff_ne_zero.mpr hm) |>
        fun h ↦ by simpa [numConstraints] using h

end numVars_gt_numConstraints

section solution

/-- The linear map from the space of coefficients to polynomials. -/
noncomputable def coeffsToPoly (k D : ℕ) : ((weigthBoundIndices k D) → F) →ₗ[F] F[X][Y] :=
  linearCombination F (fun p : weigthBoundIndices k D ↦ monomial p.1.1 p.1.2) ∘ₗ
    (linearEquivFunOnFinite F F (weigthBoundIndices k D)).symm.toLinearMap

/-- The linear map evaluating the (s,t)-th derivative coefficient at (x,y). -/
noncomputable def evalConstraint (x y : F) (s t : ℕ) : F[X][Y] →ₗ[F] F where
  toFun f := ((shift f x y).coeff t).coeff s
  map_add' f g := by simp [shift]
  map_smul' a f := by simp [shift]

/-- The linear map representing the system of linear equations. -/
noncomputable def constraintMap (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) (D : ℕ) :
  ((weigthBoundIndices k D) → F) →ₗ[F] (Fin n → constraintIndices m → F) where
  toFun c i st := evalConstraint (ωs i) (f i) st.1.1 st.1.2 (coeffsToPoly k D c)
  map_add' c d := by simp +zetaDelta at *; rfl
  map_smul' a c := by unfold evalConstraint coeffsToPoly; aesop

/-- There exists a non-zero polynomial satisfying the conditions. -/
lemma exists_nonzero_solution (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
  ∃ c : (weigthBoundIndices k (proximity_gap_degree_bound k n m)) → F,
    c ≠ 0 ∧ constraintMap k n m ωs f (proximity_gap_degree_bound k n m) c = 0 := by
      have h_kernel_nontrivial : Module.finrank F ((weigthBoundIndices k
        (proximity_gap_degree_bound k n m)) → F) >
          Module.finrank F ((Fin n → constraintIndices m → F)) := by
        convert numVars_gt_numConstraints k n m using 1
        · simp [numVars]
        · simp [numConstraints]
          norm_num [Module.finrank]
      have h_inj : ¬ Function.Injective
          (constraintMap k n m ωs f (proximity_gap_degree_bound k n m)) := by
        intro h_inj
        exact h_kernel_nontrivial.not_ge
          (LinearMap.finrank_range_of_inj h_inj ▸ Submodule.finrank_le _)
      contrapose! h_inj
      exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
        by_contra fun hx' ↦ h_inj x hx' <| by simpa using hx)

/-- The polynomial solution constructed from the non-zero kernel element. -/
noncomputable def polySol (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : F[X][Y] :=
  let c := Classical.choose (exists_nonzero_solution k n m ωs f)
  coeffsToPoly k (proximity_gap_degree_bound k n m) c

end solution

section neZero

/-- The coefficient of X^i Y^j in a linear combination of monomials is the coefficient
    of the combination. -/
lemma coeff_linearCombination_monomial (c : ℕ × ℕ →₀ F) (i j : ℕ) :
  ((linearCombination F (fun p ↦ monomial (F := F) p.1 p.2) c).coeff j).coeff i = c (i, j) := by
    simp only [linearCombination_apply, Finsupp.sum, finset_sum_coeff, coeff_smul, smul_eq_mul]
    rw [Finset.sum_eq_single (i, j)] <;> simp +contextual only [Finsupp.mem_support_iff, ne_eq,
      mul_eq_zero, false_or, Prod.forall, Prod.mk.injEq, not_and]
    · erw [coeff_monomial, if_pos rfl]; aesop
    · intro a b
      rw [monomial]
      by_cases ha : a = i <;> by_cases hb : b = j <;> simp_all [coeff_monomial]
    · exact fun h ↦ by left; exact Function.notMem_support.mp h

/-- The monomials are linearly independent. -/
lemma linearIndependent_monomials :
  LinearIndependent F (fun p : ℕ × ℕ ↦ monomial (F := F) p.1 p.2) := by
    apply _root_.linearIndependent_iff.mpr
    intro l hl
    ext ⟨i, j⟩
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    convert congr_arg (fun f ↦ (f.coeff j).coeff i) hl using 1
    convert (coeff_linearCombination_monomial l i j).symm using 1

/-- The solved polynomial is non-zero. -/
lemma polySol_ne_zero :
  polySol k n m ωs f ≠ 0 := by
    have := Classical.choose_spec (exists_nonzero_solution k n m ωs f)
    have h_inj : Function.Injective (coeffsToPoly (F := F) k
    (proximity_gap_degree_bound k n m)) := by
      have : Function.Injective (linearCombination F
        (fun p : weigthBoundIndices k (proximity_gap_degree_bound k n m) ↦
          monomial (F := F) p.1.1 p.1.2)) :=
        linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
      exact this.comp (LinearEquiv.injective _)
    exact fun h ↦ this.1 <| h_inj <| by simpa using h

end neZero

section weightedDegree

/-- The weighted degree of a monomial X^i Y^j is u*i + v*j. -/
lemma natWeightedDegree_monomial (i j u v : ℕ) :
  natWeightedDegree (monomial (F := F) i j) u v = u * i + v * j := by
    classical
    simp only [natWeightedDegree, monomial]
    refine le_antisymm ?_ ?_ <;> norm_num
    · intros b hb
      simp [coeff_monomial] at hb
      simp [← hb]
    · refine le_trans ?_ (Finset.le_sup
        (f := fun m ↦ u * (Polynomial.monomial j (Polynomial.monomial i 1)|>.coeff m|>.natDegree)
          + v * m) (b := j) ?_)
      all_goals norm_num [coeff_monomial]

/-- The weighted degree of a monomial X^i Y^j is u*i + v*j. -/
lemma natWeightedDegree_monomial_eq (i j u v : ℕ) :
  natWeightedDegree (monomial (F := F) i j) u v = u * i + v * j :=
    natWeightedDegree_monomial i j u v

/-- The weighted degree of a sum is at most the maximum of the weighted degrees. -/
lemma natWeightedDegree_add_le (p q : F[X][Y]) (u v : ℕ) :
    natWeightedDegree (p + q) u v ≤ max (natWeightedDegree p u v) (natWeightedDegree q u v) := by
  refine Finset.sup_le fun m hm ↦ ?_
  by_cases h : m ∈ p.support <;>
  by_cases h' : m ∈ q.support <;>
    simp_all only [Polynomial.mem_support_iff, coeff_add, ne_eq, le_sup_iff]
  · have h_deg : (p.coeff m + q.coeff m).natDegree ≤
        max ((p.coeff m).natDegree) ((q.coeff m).natDegree) :=
      natDegree_add_le (p.coeff m) (q.coeff m)
    cases max_cases (natDegree (p.coeff m))
      (natDegree (q.coeff m)) <;> simp_all only [sup_of_le_left, sup_eq_left, and_self,
        natWeightedDegree]
    · exact Or.inl (le_trans (add_le_add (mul_le_mul_of_nonneg_left h_deg <|
        Nat.zero_le _) le_rfl) <| Finset.le_sup (f := fun m ↦ u * natDegree
          (p.coeff m) + v * m) <| by aesop)
    · exact Or.inr (le_trans (add_le_add (mul_le_mul_of_nonneg_left h_deg <|
        Nat.zero_le _) le_rfl) <| Finset.le_sup
        (f := fun m ↦ u * natDegree (q.coeff m) + v * m) <| by aesop)
  all_goals simp_all only [not_not, add_zero, zero_add, not_false_eq_true]
  · exact Or.inl <| Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m) <| by aesop
  · exact Or.inr <| Finset.le_sup (f := fun m ↦ u * natDegree (q.coeff m) + v * m) <| by aesop
  · simp at hm

/-- The weighted degree of a sum is bounded by the supremum of the weighted degrees. -/
lemma natWeightedDegree_sum_le {ι : Type*} (s : Finset ι) (f : ι → F[X][Y]) (u v : ℕ) :
    natWeightedDegree (∑ i ∈ s, f i) u v ≤ s.sup (fun i ↦ natWeightedDegree (f i) u v) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [sum_empty, sup_empty, Nat.bot_eq_zero, nonpos_iff_eq_zero, natWeightedDegree,
      Polynomial.support_zero, coeff_zero, natDegree_zero, mul_zero, zero_add, sup_empty,
      Nat.bot_eq_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sup_insert]
    exact le_trans (natWeightedDegree_add_le _ _ _ _) (max_le_max le_rfl ih)

/-- The weighted degree of a scalar multiple is at most the weighted degree
    of the polynomial. -/
lemma natWeightedDegree_smul_le {F : Type} [Semiring F] (a : F) (p : F[X][Y]) (u v : ℕ) :
  natWeightedDegree (a • p) u v ≤ natWeightedDegree p u v := by
    simp only [natWeightedDegree, coeff_smul, Finset.sup_le_iff, Polynomial.mem_support_iff, ne_eq]
    intro b _
    exact le_trans (add_le_add
      (mul_le_mul_of_nonneg_left (natDegree_smul_le a (p.coeff b)) u.zero_le)
      (mul_le_mul_of_nonneg_left le_rfl v.zero_le))
      (Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m)
        (show b ∈ p.support from by aesop))

/-- The weighted degree of the polynomial constructed from coefficients is bounded by D. -/
lemma natWeightedDegree_coeffsToPoly_le (k D : ℕ) (c : (weigthBoundIndices k D) → F) :
    natWeightedDegree (coeffsToPoly k D c) 1 (k - 1) ≤ D := by
  have h_comb : ∃ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → F), (coeffsToPoly k D c) =
      ∑ p ∈ s, f p • (monomial (F := F) p.1 p.2) ∧ ∀ p ∈ s, p.1 + (k - 1) * p.2 ≤ D := by
    norm_num +zetaDelta at *
    refine ⟨univ.image
      (fun p : { x // x ∈ weigthBoundIndices k D } ↦ (p.val.1, p.val.2)) , ?_, ?_ ⟩;
    · use fun p ↦ if h : p ∈ univ.image
          (fun p : { x // x ∈ weigthBoundIndices k D } ↦ (p.val.1, p.val.2))
        then c ⟨p, by aesop⟩ else 0
      unfold coeffsToPoly
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        linearCombination_apply, zero_smul, implies_true, sum_fintype, univ_eq_attach, Prod.mk.eta,
        attach_image_val, dite_smul]
      refine sum_bij (fun x hx ↦ x) ?_ ?_ ?_ ?_ <;> aesop
    · unfold weigthBoundIndices at *; aesop
  obtain ⟨s, f, h₁, h₂⟩ := h_comb
  rw [h₁]
  refine le_trans (natWeightedDegree_sum_le s _ _ _) ?_
  refine Finset.sup_le fun p hp ↦ le_trans (natWeightedDegree_smul_le _ _ _ _) ?_
  rw [natWeightedDegree_monomial_eq]
  aesop

/-- The solved polynomial has weighted degree at most the proximity gap degree bound. -/
lemma polySol_weightedDegree_le :
    weightedDegree (polySol k n m ωs f) 1 (k - 1) ≤
    proximity_gap_degree_bound k n m := by
  convert Option.some_le_some.mpr
    (natWeightedDegree_coeffsToPoly_le k (proximity_gap_degree_bound k n m)
    (Classical.choose (exists_nonzero_solution k n m ωs f))) using 1
  exact weightedDegree_eq_natWeightedDegree polySol_ne_zero

end weightedDegree

section roots

/-- If constraints vanish up to order m ≥ 1, the polynomial vanishes at the point. -/
lemma eval_eq_zero_of_constraint_zero {f : F[X][Y]} {x y : F} {m : ℕ} (hm : 1 ≤ m)
    (h : ∀ s t, s + t < m → evalConstraint x y s t f = 0) : (f.eval (C y)).eval x = 0 := by
  convert h 0 0 (by linarith) using 1
  simp [evalConstraint, shift, coeff_zero_eq_eval_zero]

/-- The solved polynomial vanishes at the interpolation points if m ≠ 0. -/
lemma polySol_roots {ωs : Fin n ↪ F} {f : Fin n → F} (hm : 1 ≤ m) (i : Fin n) :
    ((polySol k n m ωs f).eval (C <| f i)).eval (ωs i) = 0 := by
  have := Classical.choose_spec (exists_nonzero_solution k n m ωs f)
  refine eval_eq_zero_of_constraint_zero hm (fun s t hst ↦ ?_)
  refine congr_fun (congr_fun this.2 i) ⟨(s, t), mem_filter.2 ⟨mem_product.mpr ?_, hst⟩⟩
  exact ⟨mem_range.2 (by linarith), mem_range.2 (by linarith)⟩

end roots

section multiplicity

/-- If `m` is the minimum of a list `l`, then `m ≤ a` for any `a ∈ l`. -/
lemma list_min_le_of_mem {l : List ℕ} {a m : ℕ} (h_min : l.min? = some m) (h_mem : a ∈ l) :
    m ≤ a := by
  rw [List.min?_eq_some_iff] at h_min; exact h_min.2 a h_mem

/-- If the `(s, t)`-coefficient of `shift Q x y` is non-zero, then the root multiplicity
    of `Q` at `(x, y)` is at most `s + t`. -/
lemma rootMultiplicity_le_of_coeff_ne_zero [DecidableEq F] {Q : F[X][Y]} {x y : F} {s t : ℕ}
    (h : Bivariate.coeff (shift Q x y) s t ≠ 0) :
    rootMultiplicity Q x y ≤ (s + t : WithTop ℕ) := by
      set g : F[X][Y] := shift Q x y;
      have h_rootMultiplicity : Polynomial.Bivariate.rootMultiplicity Q x y =
          List.min? (List.filterMap (fun p ↦
            if Bivariate.coeff g p.1 p.2 = 0 then none
            else some (p.1 + p.2)) (List.product (List.range
              (natWeightedDegree g 1 1 + 1)) (List.range (natWeightedDegree g 1 1 + 1)))) := by
        rw [Bivariate.rootMultiplicity, Bivariate.rootMultiplicity₀]
        rw [Bivariate.weightedDegree_eq_natWeightedDegree]
        · rfl
        · contrapose! h
          convert congr_arg (fun p ↦ (Polynomial.coeff p t).coeff |> fun f ↦ f s) h using 1
      obtain ⟨p, hp⟩ : ∃ p ∈ List.product (List.range (natWeightedDegree g 1 1 + 1))
          (List.range (natWeightedDegree g 1 1 + 1)), p.1 + p.2 = s + t ∧
            Bivariate.coeff g p.1 p.2 ≠ 0 := by
        use (s, t);
        have h_deg : s + t ≤ Bivariate.natWeightedDegree g 1 1 := by
          refine Finset.le_sup (f := fun m ↦ 1 * ((g.coeff m).natDegree ) + 1 * m)
              (Finset.mem_coe.mpr <| Polynomial.mem_support_iff.mpr <|
                show g.coeff t ≠ 0 from ?_) |> le_trans ?_
          · simp +zetaDelta only [ne_eq, one_mul, add_le_add_iff_right] at *
            exact le_natDegree_of_ne_zero h
          · exact fun h' => h <| by rw [Polynomial.Bivariate.coeff]; aesop
        exact ⟨List.mem_product.mpr ⟨List.mem_range.mpr (by linarith),
          List.mem_range.mpr (by linarith)⟩, rfl, h⟩
      have h_min_le : ∀ {l : List ℕ} {m : ℕ}, m ∈ l → (List.min? l).getD 0 ≤ m := by
        exact fun {l} {m} a ↦ List.min?_getD_le_of_mem a
      convert h_min_le _
      any_goals exact List.filterMap (fun p ↦ if Bivariate.coeff g p.1 p.2 = 0
        then Option.none else Option.some (p.1 + p.2)) (List.product (List.range
          (natWeightedDegree g 1 1 + 1)) (List.range (natWeightedDegree g 1 1 + 1 )))
      rotate_left
      · exact p.1 + p.2
      · rw [List.mem_filterMap]; aesop
      · cases h : List.min? (List.filterMap (fun p ↦ if Bivariate.coeff g p.1 p.2 = 0
          then Option.none else Option.some (p.1 + p.2)) (List.product (List.range
            (natWeightedDegree g 1 1 + 1)) (List.range (natWeightedDegree g 1 1 + 1)))) <;> aesop

/-- Shifting a polynomial by (x, y) results in the zero polynomial if and only if the
    original polynomial was zero. -/
lemma shift_eq_zero_iff {F : Type} [Field F] (f : F[X][Y]) (x y : F) : shift f x y = 0 ↔ f = 0 := by
  constructor <;> intro h <;> simp_all only [shift, zero_comp, Polynomial.map_zero]
  have h_comp : f.comp (Y + C (C y)) = 0 := by
    rw [Polynomial.ext_iff] at *
    intro n
    specialize h n
    simp_all [Polynomial.coeff_map]
    rw [Polynomial.comp_eq_zero_iff ] at h
    aesop
  rw [Polynomial.comp_eq_zero_iff] at h_comp
  aesop

/-- If the shifted polynomial has no non-zero coefficients of total degree less than m,
    then the root multiplicity is at least m. -/
lemma rootMultiplicity_ge_of_shift_zero [DecidableEq F] {f : F[X][Y]} {x y : F}
    {m : ℕ} (hf : f ≠ 0) (h : ∀ s t, s + t < m → ((shift f x y).coeff t).coeff s = 0) :
    m ≤ rootMultiplicity f x y := by
  by_contra h_contra
  cases h : rootMultiplicity f x y
  · simp_all only [ne_eq, Bivariate.rootMultiplicity, Option.le_none, reduceCtorEq,
      not_false_eq_true, rootMultiplicity₀]
    cases h' : weightedDegree (map (X + (C : F → F[X]) x).compRingHom
      (f.comp (Y + (C : F[X] → F[X][Y] ) (C y)))) 1 1
    · exact absurd h' (weightedDegree_ne_none _ _ _)
    · simp_all +decide only [Nat.succ_eq_add_one, List.min?_eq_none_iff, List.filterMap_eq_nil_iff,
        ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not, Prod.forall,
        List.pair_mem_product, List.mem_range, and_imp]
      have h_zero_poly : Polynomial.map (X + (C : F → F[X]) x).compRingHom
          (f.comp (Y + (C : F[X] → F[X][Y]) ((C : F → F[X]) y))) = 0 := by
        have h_zero_poly : ∀ p : F[X][Y], (∀ s t, s ≤ natWeightedDegree p 1 1 →
            t ≤ natWeightedDegree p 1 1 → Polynomial.Bivariate.coeff p s t = 0) → p = 0 := by
          intros p hp_zero
          by_contra hp_nonzero
          obtain ⟨s, t, hs⟩ : ∃ s t, Polynomial.Bivariate.coeff p s t ≠ 0 ∧
              s ≤ natWeightedDegree p 1 1 ∧ t ≤ natWeightedDegree p 1 1 := by
            obtain ⟨s, t, hs⟩ : ∃ s t, Polynomial.Bivariate.coeff p s t ≠ 0 := by
              contrapose! hp_nonzero
              ext s
              aesop
            refine ⟨s, t, hs, ?_, ?_⟩
            · refine le_trans ?_ ( Finset.le_sup <| show (t : ℕ) ∈ p.support from ?_)
              · exact le_trans (le_natDegree_of_ne_zero hs) (by linarith)
              · simp_all only [Bivariate.coeff, ne_eq, Polynomial.mem_support_iff]
                exact fun h ↦ hs <| by rw [h]; norm_num
            · refine le_trans ?_ (Finset.le_sup <| Finsupp.mem_support_iff.mpr <|
                show p.coeff t ≠ 0 from ?_)
              · norm_num
              · exact fun h ↦ hs <| by rw [Bivariate.coeff]; aesop
          exact hs.1 (hp_zero s t hs.2.1 hs.2.2)
        apply h_zero_poly
        intros s t hs ht
        convert h s t _ _ using 1
        all_goals
          rw [weightedDegree_eq_natWeightedDegree] at h'
          · grind
          · intro H
            simp [H] at h'
            exact hf (by simpa [H] using shift_eq_zero_iff f x y |>.1 H)
      simp_all only [weightedDegree, coeff_zero, natDegree_zero, mul_zero, one_mul, zero_add,
        Nat.succ_eq_add_one, List.range_one, List.map_cons, List.map_nil, List.max?_cons,
        List.max?_nil, Option.elim_none, Option.some.injEq]
      rw [Polynomial.map_eq_zero_iff] at h_zero_poly
      · simp_all only [comp_eq_zero_iff, coeff_add, map_add, false_or]
        replace h_zero_poly := congr_arg (fun p ↦ Polynomial.coeff p 1) h_zero_poly.2
        aesop
      · intro p q h_eq
        replace h_eq := congr_arg (Polynomial.comp · (X - C x)) h_eq
        simp_all [Polynomial.comp_assoc]
  · obtain ⟨deg, hdeg⟩ := Option.ne_none_iff_exists'.mp
      (weightedDegree_ne_none (Polynomial.map (X + C x).compRingHom (f.comp (Y + C (C y)))) 1 1)
    simp_all only [ne_eq, Option.some_le_some, not_le, weightedDegree, coeff_map, coe_compRingHom,
      one_mul, Nat.succ_eq_add_one]
    have h_min_ge_m : ∀ p ∈ List.filterMap (fun p ↦ if Bivariate.coeff
        (Polynomial.map (X + C x).compRingHom (f.comp (Y + C (C y)))) p.1 p.2 = 0
          then Option.none else Option.some (p.1 + p.2))
            (List.product (List.range (deg + 1)) (List.range (deg + 1))), m ≤ p := by
      simp +zetaDelta only [List.mem_filterMap, Option.ite_none_left_eq_some, Option.some.injEq,
        Prod.exists, List.pair_mem_product, List.mem_range, forall_exists_index, and_imp] at *
      intro p s t hs ht hne hp
      subst hp
      contrapose! hne
      aesop
    exact absurd (h_min_ge_m _
      (List.min?_mem (by simpa [Bivariate.rootMultiplicity, rootMultiplicity₀,
        weightedDegree, hdeg] using h)))
      (by push_neg; exact h_contra)

lemma polySol_multiplicity [DecidableEq F] (i : Fin n) :
    m ≤ rootMultiplicity (polySol k n m ωs f) (ωs i) (f i) := by
  have := Classical.choose_spec (exists_nonzero_solution k n m ωs f)
  apply rootMultiplicity_ge_of_shift_zero
  · exact polySol_ne_zero
  · simp_all only [ne_eq, constraintMap, LinearMap.coe_mk, AddHom.coe_mk, polySol]
    intro s t hst
    have := congr_fun (congr_fun this.2 i) ⟨(s, t), by
      exact Finset.mem_filter.mpr ⟨mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
        Finset.mem_range.mpr (by linarith)⟩, by linarith ⟩⟩
    aesop

end multiplicity

section divisibility

open ReedSolomon

/-- The degree of Q(X, P(X)) is bounded by the (1, k-1)-weighted degree of Q,
    provided deg(P) ≤ k - 1. -/
lemma degree_eval_le_weightedDegree (Q : F[X][Y]) (P : F[X]) (k : ℕ) (hP : P.natDegree ≤ k - 1) :
    (Q.eval P).natDegree ≤ natWeightedDegree Q 1 (k - 1) := by
  have h_deg_Q : (Q.eval P).natDegree ≤
      ((Q.toFinsupp.support).image (fun m => (Q.coeff m).natDegree + (k - 1) * m)).sup id := by
    rw [Polynomial.eval_eq_sum_range]
    refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le ?_)
    intro i hi; by_cases hi' : Q.coeff i = 0 <;> simp_all only [mem_range, Function.comp_apply,
      zero_mul, natDegree_zero, sup_image, CompTriple.comp_eq, zero_le]
    refine le_trans ?_ (Finset.le_sup
      (f := fun m ↦ (Q.coeff m).natDegree + (k - 1) * m) (show i ∈ Q.toFinsupp.support from ?_))
    · exact le_trans (Polynomial.natDegree_mul_le ..) (by norm_num; nlinarith)
    · aesop
  unfold natWeightedDegree
  aesop

/-- If Q has high multiplicity at (0,0) (meaning all coefficients c_{i,j} with i+j < m
    are zero) and P(0)=0, then Q(X, P(X)) is divisible by X^m. -/
lemma dvd_eval_of_rootMultiplicity_zero (Q : F[X][Y]) (P : F[X]) (m : ℕ)
    (hQ : ∀ i j, i + j < m → Bivariate.coeff Q i j = 0) (hP : P.coeff 0 = 0) :
    X ^ m ∣ Q.eval P := by
  have h_div_Pj : ∀ j : ℕ, X ^ j ∣ P ^ j := fun j ↦ pow_dvd_pow_of_dvd (X_dvd_iff.mpr hP) j
  have h_div_term_all : ∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 →
      X ^ m ∣ Polynomial.monomial i ((Q.coeff j).coeff i) * P ^ j := by
    intros i j hij
    have h_div_term : X ^ (i + j) ∣ Polynomial.monomial i ((Q.coeff j).coeff i) * P ^ j := by
      simp only [pow_add]
      exact mul_dvd_mul (by simp [← C_mul_X_pow_eq_monomial]) (h_div_Pj j)
    exact dvd_trans (pow_dvd_pow _ (Nat.le_of_not_lt fun h ↦ hij <| by solve_by_elim)) h_div_term
  simp only [eval_eq_sum, sum_def]
  refine Finset.dvd_sum fun n hn ↦ ?_
  rw [(Q.coeff n).as_sum_range_C_mul_X_pow]
  simp only [Finset.sum_mul, C_mul_X_pow_eq_monomial]
  classical
  exact Finset.dvd_sum fun i hi ↦
    if hi0 : (Q.coeff n).coeff i = 0 then by simp [hi0]
    else h_div_term_all i n hi0

/-- Evaluating the shifted bivariate polynomial at the shifted univariate polynomial
    is equivalent to shifting the result of the evaluation. -/
lemma eval_shifted_eq_shifted_eval (Q : F[X][Y]) (P : F[X]) (x y : F) :
  let Q_sh := (Q.comp (Y + C (C y))).map (Polynomial.compRingHom (X + C x))
  let P_sh := P.comp (X + C x) - C y
  Q_sh.eval P_sh = (Q.eval P).comp (X + C x) := by
    induction Q using Polynomial.induction_on <;> aesop

/-- If Q vanishes to order m at (x, P(x)), then Q(X, P(X)) vanishes to order m at x. -/
def HasOrderAt (Q : F[X][Y]) (x y : F) (m : ℕ) : Prop :=
  ∀ i j, i + j < m → Bivariate.coeff (shift Q x y) i j = 0

lemma orderAt_eval_ge (Q : F[X][Y]) (P : F[X]) (x : F) (m : ℕ)
    (h : HasOrderAt Q x (P.eval x) m) :
    (Q.eval P) = 0 ∨ m ≤ (Q.eval P).rootMultiplicity x := by
  set Q_sh := (Q.comp (Y + C (C (P.eval x)))).map ((X + C x).compRingHom) with hQ_sh;
  set P_sh := P.comp (X + C x) - C (P.eval x) with hP_sh;
  have hXm_div_Q_sh_eval_P_sh : X ^ m ∣ Q_sh.eval P_sh := by
    classical
    apply dvd_eval_of_rootMultiplicity_zero
    · assumption
    · simp +zetaDelta at *
      simp [coeff_zero_eq_eval_zero]
  have h_eval_shifted_eq_shifted_eval : Q_sh.eval P_sh = (Q.eval P).comp (X + C x) := by
    convert eval_shifted_eq_shifted_eval Q P x (P.eval x) using 1
  have hXm_div_Q_eval_P_comp_X_plus_C_x : X ^ m ∣ (Q.eval P).comp (X + C x) := by
    exact h_eval_shifted_eq_shifted_eval ▸ hXm_div_Q_sh_eval_P_sh
  have hX_minus_x_m_div_Q_eval_P : (X - C x) ^ m ∣ Q.eval P := by
    exact X_sub_C_pow_dvd_iff.mpr hXm_div_Q_eval_P_comp_X_plus_C_x
  by_cases h : eval P Q = 0
  · left; exact h
  · rw [le_rootMultiplicity_iff h]; tauto

/-- If a polynomial R has roots at points indexed by A with multiplicity at least m,
    and its degree is strictly less than m * |A|, then R must be the zero polynomial. -/
lemma roots_le_degree_of_deg_lt_roots (R : F[X]) (m : ℕ) (A : Finset (Fin n))
  (h_roots : ∀ i ∈ A, m ≤ R.rootMultiplicity (ωs i)) (h_deg : R.natDegree < m * A.card) :
  R = 0 := by
    classical
    have h_sum_multiplicities :
        ∑ x ∈ A.image (fun i ↦ ωs i), (R.rootMultiplicity x) ≤ R.natDegree := by
      have h_factor : ∏ x ∈ A.image (fun i ↦ ωs i), (X - C x) ^ (R.rootMultiplicity x) ∣ R := by
        refine Finset.prod_dvd_of_coprime ?_ ?_
        · intros x hx y hy hxy
          exact IsCoprime.pow (irreducible_X_sub_C _ |>
            fun h ↦ h.coprime_iff_not_dvd.mpr
              fun h' ↦ hxy <| by simpa [sub_eq_iff_eq_add] using dvd_iff_isRoot.mp h')
        · exact fun x hx ↦ R.pow_rootMultiplicity_dvd x
      have := natDegree_le_of_dvd h_factor
      by_cases h : R = 0 <;> simp_all [natDegree_prod']
    rw [Finset.sum_image <| by
      intro i hi j hj h; simpa using ωs.injective <| by aesop] at h_sum_multiplicities
    exact False.elim <| h_deg.not_ge <| h_sum_multiplicities.trans' <| by
      simpa [mul_comm] using Finset.sum_le_sum h_roots

/-- If a polynomial `q` has degree less than `n`, then interpolating its values at `n`
    points recovers `q`. -/
lemma interpolate_eq_of_degree_lt (q : F[X]) (hq : q.natDegree < n) :
  Lagrange.interpolate Finset.univ ωs (fun i ↦ q.eval (ωs i)) = q := by
    classical
    refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ?_ ?_ ?_
    · exact Finset.univ.image ωs
    · refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · rw [Finset.card_image_of_injective _ ωs.injective]
        convert Lagrange.degree_interpolate_lt _ _
        exact ωs.injective.injOn
      · exact lt_of_le_of_lt (degree_le_natDegree) (WithBot.coe_lt_coe.mpr (by
          simpa [Finset.card_image_of_injective _ ωs.injective] using hq))
    · simp +contextual only [mem_image, mem_univ, true_and, Lagrange.interpolate_apply,
        forall_exists_index, forall_apply_eq_imp_iff]
      intro i
      rw [eval_finset_sum, Finset.sum_eq_single i]
      · rw [eval_mul, Lagrange.eval_basis_self (by exact ωs.injective.injOn) (mem_univ i)]
        norm_num
      all_goals aesop

/-- The polynomial corresponding to a codeword has degree at most k-1. -/
lemma codewordToPoly_degree_le (hk : k + 1 ≤ n) (p : code ωs k) :
  (codewordToPoly p).natDegree ≤ k - 1 := by
    rw [codewordToPoly]
    obtain ⟨q, hq, hp⟩ := p.2
    have h_interpolate : (Lagrange.interpolate Finset.univ ωs.toFun) (evalOnPoints ωs q) = q := by
      convert interpolate_eq_of_degree_lt q _
      exact lt_of_le_of_lt (natDegree_le_of_degree_le <| mem_degreeLT.mp hq |> le_of_lt) hk
    rcases k <;> simp_all only [Function.Embedding.toFun_eq_coe, Lagrange.interpolate_apply,
      zero_add, degreeLT, ge_iff_le, zero_le, iInf_pos, Submodule.coe_iInf, Set.mem_iInter,
      SetLike.mem_coe, LinearMap.mem_ker, lcoeff_apply, zero_tsub, nonpos_iff_eq_zero]
    · rw [show q = 0 from Polynomial.ext hq]; norm_num
    · exact natDegree_le_iff_coeff_eq_zero.mpr hq

/-- The degree bound is strictly less than `m` times the number of agreement points,
    provided the distance is within the Johnson radius. -/
lemma sufficient_multiplicity_bound {dist : ℕ}
  (hk : k + 1 ≤ n) (hm : 1 ≤ m) (h_dist : (dist : ℝ) / n < proximity_gap_johnson k n m) :
  (proximity_gap_degree_bound k n m : ℝ) < m * (n - dist) := by
    have h_mul : (m * (n - dist) : ℝ) > (m * n * (1 - proximity_gap_johnson k n m)) := by
      rw [div_lt_iff₀] at h_dist <;> norm_num at * <;>
        nlinarith [(by norm_cast : (k : ℝ) + 1 ≤ n), (by norm_cast : (1 : ℝ) ≤ m)]
    refine lt_of_le_of_lt ?_ h_mul
    refine le_trans (Nat.floor_le ?_) ?_
    · positivity
    · unfold proximity_gap_johnson; ring_nf; norm_num
      norm_num [mul_assoc, mul_comm, mul_left_comm, ne_of_gt (zero_lt_one.trans_le hm)]

/-- If $Q$ satisfies the weighted degree bound and vanishes to order $m$ at each point
    $(\omega_i, f_i)$, and if $P$ is a codeword close enough to $f$, then $Y - P(X)$
    divides $Q(X,Y)$. -/
theorem dvd_property [DecidableEq F] (hk : k + 1 ≤ n) (hm : 1 ≤ m) (p : code ωs k)
  {Q : F[X][Y]} (hQ_ne_0 : Q ≠ 0)
  (hQ_deg : weightedDegree Q 1 (k - 1) ≤ proximity_gap_degree_bound k n m)
  (hQ_mult : ∀ i, m ≤ rootMultiplicity Q (ωs i) (f i))
  (h_dist : (hammingDist f (fun i ↦ (codewordToPoly p).eval (ωs i)) : ℝ) / n <
    proximity_gap_johnson k n m) :
  X - C (codewordToPoly p) ∣ Q := by
    contrapose! h_dist with h_distots
    have hR_nonzero : (Q.eval (codewordToPoly p)) ≠ 0 := by
      contrapose! h_distots
      exact dvd_iff_isRoot.mpr h_distots
    have hR_roots : (Q.eval (codewordToPoly p)).natDegree ≥
        m * (n - hammingDist f (fun i ↦ (codewordToPoly p).eval (ωs i))) := by
      have hR_roots : ∀ i ∈ Finset.univ.filter (fun i ↦ f i = (codewordToPoly p).eval (ωs i)), m ≤
          (Q.eval (codewordToPoly p)).rootMultiplicity (ωs i) := by
        intro i hi
        have h_root : m ≤ (Q.eval (codewordToPoly p)).rootMultiplicity (ωs i) := by
          have hQ_mult : ∀ i, HasOrderAt Q (ωs i) (f i) m := by
            intro i s t hst
            contrapose! hQ_mult
            use i
            refine fun h ↦ hst.not_ge <| le_of_not_gt fun h_lt ↦ ?_
            exact (by
              convert rootMultiplicity_le_of_coeff_ne_zero hQ_mult using 1
              cases h' : rootMultiplicity Q (ωs i) (f i)
              · aesop
              · simp_all only [ne_eq, WithTop.some_eq_coe, ENat.some_eq_coe, false_iff]
                exact_mod_cast not_le_of_gt (lt_of_lt_of_le h_lt (mod_cast h)))
          have := hQ_mult i;
          have := orderAt_eval_ge Q (codewordToPoly p) (ωs i) m (by aesop); aesop;
        exact h_root;
      have hR_roots_card : (Finset.univ.filter (fun i ↦
          f i = (codewordToPoly p).eval (ωs i))).card * m ≤
            (Q.eval (codewordToPoly p)).natDegree := by
        have hR_roots_card : (∏ i ∈ Finset.univ.filter (fun i ↦
            f i = (codewordToPoly p).eval (ωs i)), (X - C (ωs i)) ^ m) ∣
              (Q.eval (codewordToPoly p)) := by
          refine Finset.prod_dvd_of_coprime ?_ ?_
          · intros i hi j hj hij
            exact IsCoprime.pow (irreducible_X_sub_C (ωs i) |> fun hi ↦
              hi.coprime_iff_not_dvd.mpr fun h => hij <| by
                have := dvd_iff_isRoot.mp h; simp_all [sub_eq_iff_eq_add])
          · exact fun i hi ↦
              dvd_trans (pow_dvd_pow _ (hR_roots i hi)) (pow_rootMultiplicity_dvd _ _)
        have := natDegree_le_of_dvd hR_roots_card
        convert this hR_nonzero using 1
        rw [natDegree_prod _ _ fun i hi ↦ pow_ne_zero _ <| Polynomial.X_sub_C_ne_zero _]
        simp [natDegree_sub_eq_left_of_natDegree_lt]
      convert hR_roots_card.ge using 1
      simp only [hammingDist, ne_eq, mul_comm, mul_eq_mul_left_iff]
      rw [Finset.filter_not, Finset.card_sdiff]
      norm_num
      exact Or.inl (Nat.sub_sub_self (le_trans (Finset.card_le_univ _) (by norm_num)))
    have hR_deg : (Q.eval (codewordToPoly p)).natDegree ≤ proximity_gap_degree_bound k n m := by
      have hR_deg : (Q.eval (codewordToPoly p)).natDegree ≤ natWeightedDegree Q 1 (k - 1) := by
        apply degree_eval_le_weightedDegree
        exact codewordToPoly_degree_le hk p
      refine le_trans hR_deg ?_
      convert hQ_deg using 1
      rw [weightedDegree_eq_natWeightedDegree]
      · aesop
      · assumption
    contrapose! hR_roots
    refine lt_of_le_of_lt hR_deg ?_
    convert sufficient_multiplicity_bound hk hm hR_roots using 1
    rw [← @Nat.cast_lt ℝ]
    norm_num [Nat.cast_sub (show hammingDist f (fun i ↦ (codewordToPoly p).eval (ωs i)) ≤ n
      from le_trans (Finset.card_le_univ _) (by norm_num))]

end divisibility

end GuruswamiSudan

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Stefano Rocca
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate

namespace GuruswamiSudan

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

open Polynomial Polynomial.Bivariate

/--
Guruswami–Sudan conditions for the polynomial searched by the decoder.

These conditions characterize the existence of a nonzero bivariate
polynomial `Q(X,Y)` that vanishes with sufficiently high multiplicity
at all interpolation points `(ωs i, f i)`. As in the Berlekamp–Welch
case, this can be shown to be equivalent to solving a system of linear
equations.

Parameters:
* `k : ℕ` — Message length parameter of the code.
* `r : ℕ` — Multiplicity parameter; controls how many derivatives of `Q`
  must vanish at each interpolation point.
* `D : ℕ` — Degree bound for `Q` under the weighted degree measure.
* `ωs : Fin n ↪ F` — The domain of evaluation.
* `f : Fin n → F` — Received word (evaluation of the encoded polynomial,
  possibly corrupted).
* `Q : Polynomial (Polynomial F)` — The candidate bivariate polynomial
  in variables `X` and `Y`.
-/
structure Condition
  (k r D : ℕ)
  (ωs : Fin n ↪ F)
  (f : Fin n → F)
  (Q : Polynomial (Polynomial F)) where
  /-- Q ≠ 0 -/
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : Bivariate.weightedDegree Q 1 (k-1) ≤ D
  /-- (ωs i, f i) must be root of the polynomial Q. -/
  Q_roots : ∀ i, (Q.eval (C <| f i)).eval (ωs i) = 0
  /-- Multiplicity of the roots is at least r. -/
  Q_multiplicity : ∀ i, r ≤ Bivariate.rootMultiplicity Q (ωs i) (f i)

/-- Guruswami-Sudan decoder. -/
opaque decoder (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : List F[X] := sorry

/-- Each decoded codeword has to be e-far from the received message. -/
theorem decoder_mem_impl_dist
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f)
  :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by sorry

/-- If a codeword is e-far from the received message it appears in the output of
    the decoder. -/
theorem decoder_dist_impl_mem
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e)
  :
  p ∈ decoder k r D e ωs f := by sorry

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of [BCIKS20].
    D_X(m) = (m + 1/2)√ρn. -/
noncomputable def proximity_gap_degree_bound (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((((m : ℚ) + (1 : ℚ)/2)*(Real.sqrt rho))*n)

/-- The ball radius from lemma 5.3 of [BCIKS20],
    which follows from the Johnson bound.
    δ₀(ρ, m) = 1 - √ρ - √ρ/2m. -/
noncomputable def proximity_gap_johnson (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m))

section GuruswamiSudanExistence

open Polynomial BigOperators Finset Finsupp

/-- Shift a bivariate polynomial by (x, y). -/
noncomputable def shift (f : F[X][Y]) (x y : F) : F[X][Y] :=
  (f.comp (X + C (C y))).map ((X + C x).compRingHom)

/-- The monomial X^i Y^j as a bivariate polynomial. -/
noncomputable def monomial (i j : ℕ) : F[X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i 1)

section solution

/-- The set of indices `(i,j)` such that `i + (k-1)j ≤ D`. -/
def validIndices (k D : ℕ) : Finset (ℕ × ℕ) :=
  (range (D + 1)).product (range (D + 1)) |>.filter (fun x ↦ x.1 + (k - 1) * x.2 ≤ D)

/-- The number of variables in the linear system. -/
def numVars (k D : ℕ) : ℕ := (validIndices k D).card

/-- The set of derivative indices `(s,t)` such that `s + t < m`. -/
def constraintIndex (m : ℕ) : Finset (ℕ × ℕ) :=
  (range m).product (range m) |>.filter (fun x ↦ x.1 + x.2 < m)

/-- The number of constraints. -/
def numConstraints (n m : ℕ) : ℕ := n * (constraintIndex m).card

/-- The number of constraints is m(m+1)/2. -/
lemma card_constraintIndex (m : ℕ) : (constraintIndex m).card = m * (m + 1) / 2 := by
  rw [Nat.div_eq_of_eq_mul_left zero_lt_two]
  have h_eq : (constraintIndex m).card = ∑ s ∈ range m, (m - s) := by
    have h_sum : (constraintIndex m).card = ∑ s ∈ range m, (range (m - s)).card := by
      rw [show constraintIndex m = (range m).biUnion fun s ↦
        (range (m - s)).image (fun t ↦ (s, t))  from ?_, card_biUnion]
      · exact sum_congr rfl fun _ _ ↦
          card_image_of_injective _ fun _ _ h ↦ by injection h
      · exact fun i hi j hj hij ↦ disjoint_left.mpr fun x hx₁ hx₂ ↦ hij <| by aesop
      · ext ⟨s, t⟩
        simp [constraintIndex, mem_biUnion, mem_image]
        grind
    aesop
  exact h_eq.symm ▸ Nat.recOn m (by norm_num) fun n ih ↦ by
    cases n <;> simp [sum_range_succ', Nat.mul_succ] at *
    linarith

/-- The number of variables is the sum over j of the number of valid i's. -/
lemma card_validIndices_eq_sum (k D : ℕ) (hk : 1 < k) :
  (validIndices k D).card = ∑ j ∈ range (D / (k - 1) + 1), (D - (k - 1) * j + 1) := by
    have h_split : (validIndices k D).card =
        ∑ j ∈ range (D / (k - 1) + 1),
          ∑ i ∈ range (D + 1), if i + (k - 1) * j ≤ D then 1 else 0 := by
      rw [show validIndices k D =
        filter (fun p : ℕ × ℕ ↦ p.1 + (k - 1) * p.2 ≤ D)
        ((range (D + 1)).product (range (D / (k - 1) + 1))) from ?_, card_filter]
      · erw [sum_product, Finset.sum_comm]
      · ext ⟨i, j⟩
        simp [validIndices]
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
        simp [mem_Icc]
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
lemma numVars_eq_of_gt_one {k D : ℕ} (hk : 1 < k) :
    numVars k D = let L := D / (k - 1); (L + 1) * (2 * D + 2 - (k - 1) * L) / 2 := by
      convert card_validIndices_eq_sum k D hk using 1
      have h_simp : ∑ j ∈ range (D / (k - 1) + 1), (D - (k - 1) * j) =
          (D / (k - 1) + 1) * D - (k - 1) * ((D / (k - 1)) * (D / (k - 1) + 1)) / 2 := by
        have h_simp : ∑ j ∈ range (D / (k - 1) + 1), (D - (k - 1) * j) =
            ∑ j ∈ range (D / (k - 1) + 1), D -
              ∑ j ∈ range (D / (k - 1) + 1), (k - 1) * j := by
          exact eq_tsub_of_add_eq <| by
            rw [← sum_add_distrib]
            exact sum_congr rfl fun x hx ↦ tsub_add_cancel_of_le <| by
              nlinarith [mem_range.mp hx, Nat.div_mul_le_self D (k - 1)]
        simp_all [mul_comm]
        exact congrArg _ (Eq.symm <| Nat.div_eq_of_eq_mul_left zero_lt_two <| by
          rw [← sum_mul _ _ _]
          exact (D / (k - 1)).recOn (by norm_num) fun n ih ↦ by
            norm_num [range_succ] at *; linarith)
      simp_all [sum_add_distrib]
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
  interval_cases k <;> simp [numVars, validIndices]
  all_goals
  rw [filter_true_of_mem fun x hx ↦ by linarith [mem_range.mp (mem_product.mp hx |>.1)]]
  norm_num [sq, card_product]

/-- Lower bound for the square of (D+1). Specifically, (D+1)^2 > (m+1/2)^2 * (k+1) * n. -/
lemma proximity_gap_degree_bound_sq_gt {n k m : ℕ} (hn : n ≠ 0) :
    ((proximity_gap_degree_bound (n := n) k m : ℝ) + 1) ^ 2 >
      (m + 1 / 2) ^ 2 * (k + 1) * n := by
      set D := proximity_gap_degree_bound k m
      have h_bound : (D + 1 : ℝ) > (m + 1 / 2) * √((k + 1 : ℝ) * n) := by
        have hD_ge_floor : (D : ℝ) ≥ Nat.floor ((m + 1 / 2 : ℝ) * √((k + 1 : ℝ) * n)) := by
          simp +zetaDelta at *
          unfold proximity_gap_degree_bound
          norm_num [mul_assoc, mul_div_assoc, hn]
          rw [mul_comm_div]
          gcongr
          field_simp
        exact lt_of_lt_of_le (Nat.lt_floor_add_one _) (add_le_add_right hD_ge_floor _)
      nlinarith [show 0 < (m + 1 / 2 : ℝ) * √((k + 1) * n) by
        positivity, Real.mul_self_sqrt (show 0 ≤ (k + 1 : ℝ) * n by positivity)]

/-- A tighter lower bound for the number of variables when k > 1 :
    2(k-1) * numVars ≥ D(D+2). -/
lemma numVars_lower_bound_tight {k D : ℕ} (hk : 1 < k) :
    2 * (k - 1) * numVars k D ≥ D * (D + 2) := by
      have h_numVars_def : numVars k D =
          ((D / (k - 1)) + 1) * (2 * D + 2 - (k - 1) * (D / (k - 1))) / 2 :=
        numVars_eq_of_gt_one hk
      rcases k with (_|_|k) <;> simp_all [Nat.mul_succ]
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

lemma numVars_gt_numConstraints_of_gt_one {n k m : ℕ} (hn : n ≠ 0) (hk : 1 < k) (hm : m ≠ 0) :
    numVars k (proximity_gap_degree_bound (n := n) k m) > numConstraints n m := by
      set D := proximity_gap_degree_bound (n := n) k m
      have hD : ((D + 1)^2 : ℝ) > ((m : ℝ) + 1 / 2)^2 * (k + 1) * n := by
        convert proximity_gap_degree_bound_sq_gt hn using 1
      have h_ineq : 2 * (k - 1) * numVars k D > (k - 1) * n * m * (m + 1) := by
        have h_ineq : 2 * (k - 1) * numVars k D ≥ (D : ℝ) * (D + 2) := by
          convert numVars_lower_bound_tight hk using 1
          norm_cast
          rw [Int.subNatNat_of_le] <;> norm_cast
          linarith
        have h_ineq : (D : ℝ) * (D + 2) > (k - 1) * n * m * (m + 1) := by
          nlinarith [show (k : ℝ) ≥ 2 by norm_cast, show (m : ℝ) ≥ 1 by
            exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hm), show (n : ℝ) ≥ 1 by
              exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn), mul_le_mul_of_nonneg_left
                (show (m : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hm))
                  (show (n : ℝ) ≥ 0 by positivity)]
        norm_cast at *;
        rw [Int.subNatNat_of_le] at * <;> (norm_cast at *; linarith)
      have h_div : numVars k D > n * m * (m + 1) / 2 := by
        exact Nat.div_lt_of_lt_mul <| by nlinarith [Nat.sub_pos_of_lt hk]
      convert h_div using 1
      convert congr_arg (fun x : ℕ ↦ n * x) (card_constraintIndex m) using 1
      rw [← Nat.mul_div_assoc] <;> ring_nf
      exact even_iff_two_dvd.mp (by simp [parity_simps])

lemma numVars_gt_numConstraints (n k m : ℕ) :
  numVars k (proximity_gap_degree_bound (n := n) k m) > numConstraints n m := by
  by_cases hk : k ≤ 1
  · interval_cases k <;> norm_num [numVars_eq_sq, numConstraints]
    · unfold proximity_gap_degree_bound
      norm_num
      have h_constraint_card : (constraintIndex m).card = m * (m + 1) / 2 := by
        exact card_constraintIndex m
      rcases n with (_ | n) <;> rcases m with (_ | m) <;> norm_num at *
      · norm_num [card_constraintIndex]
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
    · by_cases hn : n = 0
      · aesop
      · by_cases hm : m = 0
        · unfold constraintIndex; aesop
        · have h_ineq : (m + 1 / 2 : ℝ) ^ 2 * 2 * n > n * m * (m + 1) / 2 := by
            nlinarith [show (m : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hm),
              show (n : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn),
                mul_pos (show (m : ℝ) > 0 by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
                  (show (n : ℝ) > 0 by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
          have h_ineq : (n * m * (m + 1) / 2 : ℝ) <
              ((proximity_gap_degree_bound (n := n) 1 m + 1) : ℝ) ^ 2 := by
            refine lt_of_lt_of_le h_ineq ?_
            convert proximity_gap_degree_bound_sq_gt hn |> le_of_lt using 1
            ring
          rw [div_lt_iff₀] at h_ineq <;> norm_cast at *
          rw [card_constraintIndex]
          nlinarith [Nat.div_mul_le_self (m * (m + 1)) 2]
  · by_cases hn : n = 0 <;> by_cases hm : m = 0 <;> simp_all [numConstraints]
    · exact card_pos.mpr ⟨⟨0, 0⟩,
        mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr
          <| Nat.succ_pos _, mem_range.mpr <| Nat.succ_pos _⟩, by norm_num⟩⟩
    · exact card_pos.mpr ⟨⟨0, 0⟩, mem_filter.mpr ⟨mem_product.mpr
        ⟨mem_range.mpr <| Nat.succ_pos _, mem_range.mpr <| Nat.succ_pos _⟩, by
          norm_num⟩⟩
    · exact lt_of_lt_of_le (by simp [constraintIndex])
        (Nat.pos_of_ne_zero (ne_of_gt (card_pos.mpr ⟨(0, 0),
          mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (Nat.succ_pos _),
            mem_range.mpr (Nat.succ_pos _)⟩, by norm_num⟩⟩)))
    · exact numVars_gt_numConstraints_of_gt_one hn hk hm |> fun h ↦ by
        simpa [numConstraints] using h

/-- The linear map from the space of coefficients to polynomials. -/
noncomputable def coeffsToPoly (k D : ℕ) : ((validIndices k D) → F) →ₗ[F] F[X][Y] :=
  linearCombination F (fun p : validIndices k D ↦ monomial p.1.1 p.1.2) ∘ₗ
    (linearEquivFunOnFinite F F (validIndices k D)).symm.toLinearMap

/-- The linear map evaluating the (s,t)-th derivative coefficient at (x,y). -/
noncomputable def evalConstraint (x y : F) (s t : ℕ) : F[X][Y] →ₗ[F] F where
  toFun f := ((shift f x y).coeff t).coeff s
  map_add' f g := by simp [shift]
  map_smul' a f := by simp [shift]

/-- The linear map representing the system of linear equations. -/
noncomputable def constraintMap (n k m D : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
  ((validIndices k D) → F) →ₗ[F] (Fin n → constraintIndex m → F) where
  toFun c i st := evalConstraint (ωs i) (f i) st.1.1 st.1.2 (coeffsToPoly k D c)
  map_add' c d := by simp +zetaDelta at *; rfl
  map_smul' a c := by unfold evalConstraint coeffsToPoly; aesop

omit [DecidableEq F]
/-- There exists a non-zero polynomial Q satisfying the conditions. -/
lemma exists_nonzero_solution (n k m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
  ∃ c : (validIndices k (proximity_gap_degree_bound (n := n) k m)) → F,
    c ≠ 0 ∧ constraintMap n k m (proximity_gap_degree_bound (n := n) k m) ωs f c = 0 := by
      have h_kernel_nontrivial : Module.finrank F ((validIndices k
        (proximity_gap_degree_bound (n := n) k m)) → F) >
          Module.finrank F ((Fin n → constraintIndex m → F)) := by
        convert numVars_gt_numConstraints n k m using 1
        · simp [numVars]
        · simp [numConstraints]
          norm_num [Module.finrank]
      have h_inj : ¬ Function.Injective (constraintMap n k m
          (proximity_gap_degree_bound (n := n) k m) ωs f) := by
        intro h_inj
        have := LinearMap.finrank_range_of_inj h_inj
        exact h_kernel_nontrivial.not_ge (this ▸ Submodule.finrank_le _)
      contrapose! h_inj
      exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
        by_contra fun hx' ↦ h_inj x hx' <| by simpa using hx)

/-- The polynomial solution constructed from the non-zero kernel element. -/
noncomputable def solvedPoly (n k m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : F[X][Y] :=
  let c := Classical.choose (exists_nonzero_solution n k m ωs f)
  coeffsToPoly k (proximity_gap_degree_bound k m) c

end solution

section neZero

/-- The coefficient of X^i Y^j in a linear combination of monomials is the coefficient
    of the combination. -/
lemma coeff_linearCombination_monomial (c : ℕ × ℕ →₀ F) (i j : ℕ) :
  ((linearCombination F (fun p ↦ monomial (F := F) p.1 p.2) c).coeff j).coeff i = c (i, j) := by
    simp [linearCombination_apply, Finsupp.sum]
    rw [Finset.sum_eq_single (i, j)] <;> simp +contextual
    · erw [coeff_monomial, if_pos rfl]; aesop
    · intro a b
      rw [monomial]
      by_cases ha : a = i <;> by_cases hb : b = j <;> simp_all [coeff_monomial]

/-- The monomials are linearly independent. -/
lemma linearIndependent_monomials :
  LinearIndependent F (fun p : ℕ × ℕ ↦ monomial (F := F) p.1 p.2) := by
    apply linearIndependent_iff.mpr
    intro l hl
    ext ⟨i, j⟩
    simp_all
    convert congr_arg (fun f ↦ (f.coeff j).coeff i) hl using 1
    convert (coeff_linearCombination_monomial l i j).symm using 1

/-- The solved polynomial is non-zero. -/
lemma solvedPoly_ne_zero {n k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  solvedPoly n k m ωs f ≠ 0 := by
    have := Classical.choose_spec (exists_nonzero_solution n k m ωs f)
    have h_inj : Function.Injective (coeffsToPoly (F := F) k
    (proximity_gap_degree_bound (n := n) k m)) := by
      have h_linear_combination_injective : Function.Injective (linearCombination F
        (fun p : validIndices k (proximity_gap_degree_bound (n := n) k m) ↦
          monomial (F := F) p.1.1 p.1.2)) :=
        linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
      exact h_linear_combination_injective.comp (LinearEquiv.injective _)
    exact fun h ↦ this.1 <| h_inj <| by simpa using h

end neZero

section weightedDegree

/-- The weighted degree of a monomial X^i Y^j is u*i + v*j. -/
lemma natWeightedDegree_monomial (i j u v : ℕ) :
  natWeightedDegree (monomial (F := F) i j) u v = u * i + v * j := by
    simp [natWeightedDegree, monomial]
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
  natWeightedDegree (monomial (F := F) i j) u v = u * i + v * j := by
    convert natWeightedDegree_monomial i j u v using 1
    infer_instance

/-- The weighted degree of a sum is at most the maximum of the weighted degrees. -/
lemma natWeightedDegree_add_le (p q : F[X][Y]) (u v : ℕ) :
    natWeightedDegree (p + q) u v ≤ max (natWeightedDegree p u v) (natWeightedDegree q u v) := by
  refine Finset.sup_le fun m hm ↦ ?_
  by_cases h : m ∈ p.support <;>
  by_cases h' : m ∈ q.support <;> simp_all [coeff_add]
  · have h_deg : (p.coeff m + q.coeff m).natDegree ≤
        max ((p.coeff m).natDegree) ((q.coeff m).natDegree) := by
      exact natDegree_add_le (p.coeff m) (q.coeff m)
    cases max_cases (natDegree (p.coeff m))
      (natDegree (q.coeff m)) <;> simp_all [natWeightedDegree]
    · exact Or.inl (le_trans (add_le_add (mul_le_mul_of_nonneg_left h_deg <|
        Nat.zero_le _) le_rfl) <| Finset.le_sup (f := fun m ↦ u * natDegree
          (p.coeff m) + v * m) <| by aesop)
    · exact Or.inr (le_trans (add_le_add (mul_le_mul_of_nonneg_left h_deg <|
        Nat.zero_le _) le_rfl) <| Finset.le_sup
        (f := fun m ↦ u * natDegree (q.coeff m) + v * m) <| by aesop)
  · exact Or.inl <| Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m) <| by aesop
  · exact Or.inr <| Finset.le_sup (f := fun m ↦ u * natDegree (q.coeff m) + v * m) <| by aesop

/-- The weighted degree of a sum is bounded by the supremum of the weighted degrees. -/
lemma natWeightedDegree_sum_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → F[X][Y]) (u v : ℕ) :
    natWeightedDegree (∑ i ∈ s, f i) u v ≤ s.sup (fun i ↦ natWeightedDegree (f i) u v) := by
  induction s using Finset.induction <;> simp_all
  · simp [natWeightedDegree]
  · have h_sum : natWeightedDegree (f ‹_› + ∑ i ∈ ‹Finset ι›, f i) u v ≤
      max (natWeightedDegree (f ‹_›) u v) (natWeightedDegree (∑ i ∈ ‹Finset ι›, f i) u v) := by
      (expose_names; exact natWeightedDegree_add_le (f a) (∑ i ∈ s, f i) u v)
    cases max_cases (natWeightedDegree (f ‹_›) u v)
      (natWeightedDegree (∑ i ∈ ‹Finset ι›, f i) u v) <;> [left; right] <;> linarith

/-- The weighted degree of a scalar multiple is at most the weighted degree
    of the polynomial. -/
lemma natWeightedDegree_smul_le {F : Type} [Semiring F] (a : F) (p : F[X][Y]) (u v : ℕ) :
  natWeightedDegree (a • p) u v ≤ natWeightedDegree p u v := by
    simp [natWeightedDegree]
    intro b _
    exact le_trans (add_le_add
      (mul_le_mul_of_nonneg_left (natDegree_smul_le a (p.coeff b)) u.zero_le)
      (mul_le_mul_of_nonneg_left le_rfl v.zero_le))
      (Finset.le_sup (f := fun m ↦ u * natDegree (p.coeff m) + v * m)
        (show b ∈ p.support from by aesop))

/-- The weighted degree of the polynomial constructed from coefficients is bounded by D. -/
lemma natWeightedDegree_coeffsToPoly_le (k D : ℕ) (c : (validIndices k D) → F) :
    natWeightedDegree (coeffsToPoly k D c) 1 (k - 1) ≤ D := by
  have h_comb : ∃ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → F), (coeffsToPoly k D c) =
      ∑ p ∈ s, f p • (monomial (F := F) p.1 p.2) ∧ ∀ p ∈ s, p.1 + (k - 1) * p.2 ≤ D := by
    norm_num +zetaDelta at *
    refine ⟨univ.image
      (fun p : { x // x ∈ validIndices k D } ↦ (p.val.1, p.val.2)) , ?_, ?_ ⟩;
    · use fun p ↦ if h : p ∈ univ.image
          (fun p : { x // x ∈ validIndices k D } ↦ (p.val.1, p.val.2))
        then c ⟨p, by aesop⟩ else 0
      unfold coeffsToPoly
      simp [linearCombination_apply, sum_fintype]
      refine sum_bij (fun x hx ↦ x) ?_ ?_ ?_ ?_ <;> aesop
    · unfold validIndices at *; aesop
  obtain ⟨s, f, h₁, h₂⟩ := h_comb
  rw [h₁]
  refine le_trans (natWeightedDegree_sum_le s _ _ _) ?_
  refine Finset.sup_le fun p hp ↦ le_trans (natWeightedDegree_smul_le _ _ _ _) ?_
  rw [natWeightedDegree_monomial_eq]
  aesop

/-- The solved polynomial has weighted degree at most the proximity gap degree bound. -/
lemma solvedPoly_weightedDegree_le {n k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
    weightedDegree (solvedPoly n k m ωs f) 1 (k - 1) ≤
    proximity_gap_degree_bound (n := n) k m := by
  convert Option.some_le_some.mpr
    (natWeightedDegree_coeffsToPoly_le k (proximity_gap_degree_bound k m)
    (Classical.choose (exists_nonzero_solution n k m ωs f))) using 1
  exact weightedDegree_eq_natWeightedDegree solvedPoly_ne_zero

end weightedDegree

section roots

omit [DecidableEq F]
/-- If constraints vanish up to order m ≥ 1, the polynomial vanishes at the point. -/
lemma eval_eq_zero_of_constraint_zero {f : F[X][Y]} {x y : F} {m : ℕ} (hm : 1 ≤ m)
    (h : ∀ s t, s + t < m → evalConstraint x y s t f = 0) : (f.eval (C y)).eval x = 0 := by
  convert h 0 0 (by linarith) using 1
  simp [evalConstraint, shift, coeff_zero_eq_eval_zero]

/-- The solved polynomial vanishes at the interpolation points if m ≠ 0. -/
lemma solvedPoly_roots {n k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} (hm : m ≠ 0) (i : Fin n) :
    ((solvedPoly n k m ωs f).eval (C <| f i)).eval (ωs i) = 0 := by
  have := Classical.choose_spec (exists_nonzero_solution n k m ωs f)
  refine eval_eq_zero_of_constraint_zero (Nat.pos_of_ne_zero hm) (fun s t hst ↦ ?_)
  refine congr_fun (congr_fun this.2 i) ⟨(s, t), mem_filter.2 ⟨mem_product.mpr ?_, hst⟩⟩
  exact ⟨mem_range.2 (by linarith), mem_range.2 (by linarith)⟩

end roots

section multiplicity

/-- rootMultiplicity₀ computes the total degree. -/
lemma rootMultiplicity₀_eq_totalDegree {f : F[X][Y]} (hf : f ≠ 0) :
    rootMultiplicity₀ f = some (totalDegree f) := by
  have h_max_eq : ∀ (f : F[X][Y]), f ≠ 0 → ∃ (deg : ℕ), (weightedDegree f 1 1) =
      some deg ∧ (List.max? (List.map (fun x ↦ if coeff f x.1 x.2 ≠ 0 then x.1 + x.2 else 0)
        (List.product (List.range (deg + 1)) (List.range (deg + 1))))) =
          some (totalDegree f) := by
    intros f hf_nonzero
    obtain ⟨deg, hdeg⟩ : ∃ (deg : ℕ),
        (weightedDegree f 1 1) = some deg ∧ deg = totalDegree f := by
      convert weightedDegree_eq_natWeightedDegree hf_nonzero using 1
      rw [total_deg_as_weighted_deg]
      exact ⟨fun ⟨deg, hdeg₁, hdeg₂⟩ ↦ hdeg₁.trans (hdeg₂.symm ▸ rfl), fun hdeg ↦ ⟨_, hdeg, rfl⟩⟩
    have h_max : ∃ x ∈ List.product (List.range (deg + 1)) (List.range (deg + 1)),
        (if coeff f x.1 x.2 ≠ 0 then x.1 + x.2 else 0) = totalDegree f := by
      obtain ⟨i, j, hij⟩ : ∃ i j, coeff f i j ≠ 0 ∧ i + j = totalDegree f := by
        obtain ⟨i, j, hij⟩ : ∃ i j, (f.coeff j).coeff i ≠ 0 ∧ i + j = totalDegree f := by
          have h_support : ∃ p ∈ f.support, (f.coeff p).natDegree + p = totalDegree f := by
            have h_support : ∃ p ∈ f.support, ∀ q ∈ f.support, (f.coeff q).natDegree + q ≤
                (f.coeff p).natDegree + p := by
              apply_rules [exists_max_image]
              exact nonempty_of_ne_empty (by aesop)
            exact ⟨h_support.choose, h_support.choose_spec.1,
                le_antisymm (Finset.le_sup
                  (f := fun p ↦ (f.coeff p).natDegree + p) h_support.choose_spec.1)
                    (Finset.sup_le fun q hq ↦ h_support.choose_spec.2 q hq)⟩
          obtain ⟨p, hp₁, hp₂⟩ := h_support
          use (f.coeff p).natDegree, p
          aesop
        exact ⟨i, j, hij⟩
      exact ⟨⟨i, j⟩, by
        erw [List.mem_product]
        exact ⟨List.mem_range.mpr (by linarith), List.mem_range.mpr (by linarith)⟩, by aesop⟩
    refine ⟨ deg, hdeg.1, (List.max?_eq_some_iff
      (fun a ↦ le_rfl) (fun a b ↦ max_choice a b) (fun a b c ↦ Nat.max_le)).mpr ?_ ⟩
    simp +zetaDelta at *
    refine ⟨h_max, fun b x y hx hy hb ↦ ?_⟩
    subst hb
    split_ifs <;> simp_all [Bivariate.coeff]
    exact le_sup (f := fun m ↦ (f.coeff m).natDegree + m)
      (show y ∈ f.support from by aesop) |>
        le_trans (by linarith [le_natDegree_of_ne_zero ‹_›])
  unfold rootMultiplicity₀
  specialize h_max_eq f hf
  aesop

/-- If all coefficients of degree less than m are zero, the total degree is at least m. -/
lemma totalDegree_ge_m_of_forall_coeff_zero_lt_m {f : F[X][Y]} (hf : f ≠ 0) (m : ℕ)
    (h : ∀ s t, s + t < m → Bivariate.coeff f s t = 0) : m ≤ totalDegree f := by
  have h_totalDegree_ge_m : ∃ p ∈ f.support, (f.coeff p).natDegree + p ≥ m := by
    by_contra h_contra
    push_neg at h_contra
    have h_zero : ∀ p ∈ f.support, (f.coeff p).natDegree + p < m := by assumption
    refine hf (ext fun p ↦ ?_)
    by_cases hp : p ∈ f.support <;> simp_all [Bivariate.coeff]
    exact absurd (h ((f.coeff p).natDegree) p (h_zero p hp)) (by simp [coeff_natDegree, hp])
  exact h_totalDegree_ge_m.choose_spec.2.trans (Finset.le_sup
    (f := fun x ↦ (f.coeff x).natDegree + x) h_totalDegree_ge_m.choose_spec.1)

/-- The solved polynomial has root multiplicity at least m at each point (ωs i, f i). -/
lemma solvedPoly_multiplicity {n k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} (i : Fin n) :
    m ≤ rootMultiplicity (solvedPoly n k m ωs f) (ωs i) (f i) := by
  let Q := solvedPoly n k m ωs f
  have h_shift : shift Q (ωs i) (f i) ≠ 0 := by
    intro h
    have h_shift_nonzero : ∀ x y : F, shift Q x y = 0 → Q = 0 := by
      intro x y hxy
      have h_shift_nonzero : Q.comp (X + C (C y)) = 0 := by
        have h_shift_nonzero : Q.comp (X + C (C y)) = (shift Q x y).map (X - C x).compRingHom := by
          unfold shift; ext; simp; ring_nf; simp [comp_assoc]
        aesop
      exact comp_X_add_C_eq_zero_iff.mp h_shift_nonzero
    exact solvedPoly_ne_zero <| h_shift_nonzero _ _ h
  rw [Bivariate.rootMultiplicity]
  change m ≤ rootMultiplicity₀ (shift Q (ωs i) (f i))
  rw [rootMultiplicity₀_eq_totalDegree h_shift]
  have := Classical.choose_spec (exists_nonzero_solution n k m ωs f)
  refine totalDegree_ge_m_of_forall_coeff_zero_lt_m (F := F) h_shift _ (fun s t hst ↦ ?_)
  refine congr_fun (congr_fun this.2 i) ⟨(s, t), ?_⟩
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_range.mpr (by linarith), mem_range.mpr (by linarith)⟩, hst⟩

end multiplicity

/-- Existence of the Guruswami-Sudan polynomial (proven for m ≠ 0). -/
theorem guruswami_sudan_for_proximity_gap_existence {n k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q, Condition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  by_cases hm : m = 0
  · sorry
  · use solvedPoly n k m ωs f
    exact ⟨solvedPoly_ne_zero, solvedPoly_weightedDegree_le,
      solvedPoly_roots hm, solvedPoly_multiplicity⟩

end GuruswamiSudanExistence

section GuruswamiSudanProperty

/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, ρ] such that Δ(w, P) ≤ δ₀(ρ, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y]. -/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {Q : F[X][X]}
  {p : ReedSolomon.code ωs n}
  (h : Δ₀(f, (ReedSolomon.codewordToPoly p).eval ∘ f) ≤ proximity_gap_johnson (n := n) k m)
  :
  ((X : F[X][X]) - C (ReedSolomon.codewordToPoly p)) ∣ Q := by sorry

end GuruswamiSudanProperty

end GuruswamiSudan

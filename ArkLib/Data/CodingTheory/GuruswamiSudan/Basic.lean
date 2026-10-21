/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefano Rocca
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Real.Sqrt

public import ArkLib.Data.CodingTheory.Basic.DecodingRadius
public import ArkLib.Data.CodingTheory.Basic.Distance
public import ArkLib.Data.CodingTheory.Basic.LinearCode
public import ArkLib.Data.CodingTheory.Basic.RelativeDistance
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.Polynomial.Bivariate
/-! # Guruswami-Sudan Basics

Degree bounds and variable/constraint counting for the Guruswami-Sudan interpolation system, in
the parametrization used by the affine-line proximity-gap argument: the system asks for a nonzero
bivariate polynomial with a `(1, k-1)`-weighted degree bound that vanishes with multiplicity `m`
at `n` prescribed points, and it is solvable as soon as it has more variables than constraints.

## Main definitions and results

- `proximity_gap_degree_bound`, `gs_degree_bound` — the `D_X`-style weighted-degree bounds, with
  reduced rate `(k+1)/n` and `k/n` respectively.
- `weightBoundIndices`, `numVars`, `numConstraints` — the monomial index set of the system and
  the two counts.
- `numVars_gt_numConstraints_of_mul_lt` — the shared counting core: the system is
  underdetermined as soon as `D * (D + 2) > (k - 1) * n * m * (m + 1)`.
- `sum_snd_weightBoundIndices_le` — the first-moment bound `6 (k-1)² · Σ j ≤ (D + 1)³` on the
  total `Y`-degree of the index set.

## References

- [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*
  (ePrint 2020/654): Lemma 5.3 for the degree bounds, Appendix B.1 for the first-moment bound.
-/

@[expose] public section


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

/-- Degree bound with ρ = k/n (matching RS code rate). The original
    `proximity_gap_degree_bound` uses ρ = (k+1)/n which is conservative. -/
noncomputable def gs_degree_bound (k n m : ℕ) : ℕ :=
  let rho := (k : ℚ) / n
  ⌊(m + 1 / 2) * √ rho * n⌋₊

/-- Johnson radius with ρ = k/n. Approaches `1 - √(k/n)` as `m → ∞`. -/
noncomputable def gs_johnson (k n m : ℕ) : ℝ :=
  let rho := (k : ℚ) / n
  1 - √ rho - √ rho / (2 * m)

/-- The GS degree bound with m=1 divided by (k-1) is less than F
    when |F| ≥ 5 and the RS code is non-degenerate (k+1 ≤ n ≤ F). -/
lemma gs_degree_bound_div_lt {k n F : ℕ} (hk : 2 ≤ k) (hn : n ≤ F) (hF : 5 ≤ F)
    (hkn : k + 1 ≤ n) :
    gs_degree_bound k n 1 / (k - 1) < F := by
  have hk1 : 0 < k - 1 := by omega
  rw [Nat.div_lt_iff_lt_mul hk1]
  unfold gs_degree_bound; dsimp only
  rw [Nat.floor_lt (by positivity)]
  have harith : 9 * k * n < 4 * (F * (k - 1)) ^ 2 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    have h5 : 5 ≤ F * (j + 1) := hF.trans (Nat.le_mul_of_pos_right F (Nat.succ_pos j))
    calc 9 * (j + 1 + 1) * n ≤ 9 * (j + 1 + 1) * F := Nat.mul_le_mul_left _ hn
      _ < 4 * (j + 1) * (5 * F) := by
        rw [← mul_assoc]; exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ 4 * (j + 1) * (F * (j + 1) * F) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right F h5)
      _ = 4 * (F * (j + 1)) ^ 2 := by ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity) ?_
  have hsq : ((↑(1 : ℕ) + 1 / 2) * √↑(↑k / ↑n : ℚ) * ↑n : ℝ) ^ 2 = 9 / 4 * k * n := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    push_cast
    field_simp
    ring
  rw [hsq]
  have : ((9 * k * n : ℕ) : ℝ) < ((4 * (F * (k - 1)) ^ 2 : ℕ) : ℝ) := by exact_mod_cast harith
  push_cast at this ⊢
  linarith only [this]

namespace GuruswamiSudan

/-- The monomial X^i Y^j as a bivariate polynomial. -/
noncomputable def monomial (i j : ℕ) : F[X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i 1)

section numVars

/-- Given a nonnegative integer `D`, it is the set of indices `(i,j)` such
    that `i + (k - 1) * j ≤ D`. -/
def weightBoundIndices (k D : ℕ) : Finset (ℕ × ℕ) :=
  (range (D + 1)).product (range (D + 1)) |>.filter (fun x ↦ x.1 + (k - 1) * x.2 ≤ D)

/-- The number of variables in the Guruswami-Sudan linear system. -/
def numVars (k D : ℕ) : ℕ := (weightBoundIndices k D).card

/-- The index set of the Guruswami-Sudan system, with the range of the `Y`-degree already
truncated to the values that can actually occur. -/
lemma weightBoundIndices_eq_filter_product (D : ℕ) (hk : 1 < k) :
    weightBoundIndices k D =
      filter (fun p : ℕ × ℕ ↦ p.1 + (k - 1) * p.2 ≤ D)
        ((range (D + 1)).product (range (D / (k - 1) + 1))) := by
  ext ⟨i, j⟩
  simp only [weightBoundIndices, product_eq_sprod, mem_filter, mem_product, mem_range,
    and_congr_left_iff, and_congr_right_iff]
  intro h _
  have hj : (k - 1) * j ≤ D := le_of_add_le_right h
  exact iff_of_true
    (Nat.lt_succ_of_le ((Nat.le_mul_of_pos_left j (Nat.sub_pos_of_lt hk)).trans hj))
    (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hk)).2
      ((Nat.mul_comm _ _).le.trans hj)))

/-- The number of variables is the sum over j of the number of valid i's. -/
lemma card_weightBoundIndices_eq_sum (D : ℕ) (hk : 1 < k) :
    (weightBoundIndices k D).card = ∑ j ∈ range (D / (k - 1) + 1), (D - (k - 1) * j + 1) := by
    have h_split : (weightBoundIndices k D).card =
        ∑ j ∈ range (D / (k - 1) + 1),
          ∑ i ∈ range (D + 1), if i + (k - 1) * j ≤ D then 1 else 0 := by
      rw [weightBoundIndices_eq_filter_product D hk, card_filter]
      erw [sum_product, Finset.sum_comm]
    have h_inner : ∀ j ∈ range (D / (k - 1) + 1), ∑ i ∈ range (D + 1),
        (if i + (k - 1) * j ≤ D then 1 else 0) = (D - (k - 1) * j) + 1 := by
      intro j hj
      have hjle : j ≤ D / (k - 1) := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hcj : (k - 1) * j ≤ D := by
        calc
          (k - 1) * j ≤ (k - 1) * (D / (k - 1)) := Nat.mul_le_mul_left _ hjle
          _ ≤ D := Nat.mul_div_le D (k - 1)
      have h_filter : filter (fun i ↦ i + (k - 1) * j ≤ D) (range (D + 1)) =
          Icc 0 (D - (k - 1) * j) := by
        ext i
        simp only [mem_filter, mem_range, mem_Icc, zero_le, true_and]
        exact ⟨fun h ↦ Nat.le_sub_of_add_le h.2, fun hi ↦
          ⟨Nat.lt_succ_of_le (hi.trans (Nat.sub_le _ _)), Nat.add_le_of_le_sub hcj hi⟩⟩
      rw [← card_filter, h_filter, Nat.card_Icc, Nat.sub_zero]
    exact h_split.trans (sum_congr rfl h_inner)

/-- Closed form for the number of variables when k > 1. -/
lemma numVars_eq_of_gt_one {D : ℕ} (hk : 1 < k) :
    numVars k D = let L := D / (k - 1); (L + 1) * (2 * D + 2 - (k - 1) * L) / 2 := by
  rw [numVars, card_weightBoundIndices_eq_sum D hk]
  dsimp only
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hdm := Nat.div_add_mod D c
  generalize D / c = L at hdm ⊢
  generalize D % c = r at hdm
  subst hdm
  have h1 : 2 * (c * L + r) + 2 - c * L = c * L + 2 * r + 2 := by omega
  rw [h1]
  obtain ⟨T, hT⟩ := Nat.even_mul_succ_self L
  have hX : (L + 1) * (c * L + 2 * r + 2) = 2 * (c * T + (L + 1) * (r + 1)) := by
    calc _ = c * (L * (L + 1)) + 2 * ((L + 1) * (r + 1)) := by ring
      _ = _ := by rw [hT]; ring
  rw [hX, Nat.mul_div_cancel_left _ two_pos, ← Finset.sum_range_reflect]
  have hterm : ∀ j ∈ range (L + 1), c * L + r - c * (L + 1 - 1 - j) + 1 = c * j + (r + 1) := by
    intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (mem_range.mp hj))
    rw [show j + i + 1 - 1 - j = i by omega, mul_add]
    generalize c * j = a
    generalize c * i = b
    omega
  have hsum := Finset.sum_range_id_mul_two (L + 1)
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, sum_const, card_range,
    smul_eq_mul, Nat.add_sub_cancel, mul_comm (L + 1) L, hT] at *
  congr 2
  omega

/-- The number of variables is (D+1)^2 when k ≤ 1. -/
lemma numVars_eq_sq {k D : ℕ} (hk : k ≤ 1) : numVars k D = (D + 1) ^ 2 := by
  interval_cases k
  all_goals
  simp only [numVars, weightBoundIndices, tsub_self, zero_mul, add_zero, product_eq_sprod]
  norm_num
  rw [filter_true_of_mem fun x hx ↦ by linarith [mem_range.mp (mem_product.mp hx |>.1)]]
  norm_num [sq, card_product]

/-- A tighter lower bound for the number of variables when k > 1 :
    2(k-1) * numVars ≥ D(D+2). -/
lemma numVars_lower_bound_tight {D : ℕ} (hk : 1 < k) :
    2 * (k - 1) * numVars k D ≥ D * (D + 2) := by
  rw [numVars_eq_of_gt_one hk]
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  dsimp only
  rw [Nat.add_sub_cancel]
  have hdm := Nat.div_add_mod D c
  have hrc := Nat.mod_lt D (by omega : 0 < c)
  generalize D / c = L at hdm ⊢
  generalize D % c = r at hdm hrc
  subst hdm
  obtain ⟨s, rfl⟩ : ∃ s, c = r + 1 + s := ⟨c - (r + 1), by omega⟩
  generalize hM : (r + 1 + s) * L = M
  have h1 : 2 * (M + r) + 2 - M = M + 2 * r + 2 := by omega
  rw [h1]
  obtain ⟨T, hT⟩ := Nat.even_mul_succ_self L
  have hX : (L + 1) * (M + 2 * r + 2) = 2 * ((r + 1 + s) * T + (L + 1) * (r + 1)) := by
    calc _ = (r + 1 + s) * (L * (L + 1)) + 2 * ((L + 1) * (r + 1)) := by rw [← hM]; ring
      _ = _ := by rw [hT]; ring
  rw [hX, Nat.mul_div_cancel_left _ two_pos]
  have hY : 2 * (r + 1 + s) * ((r + 1 + s) * T + (L + 1) * (r + 1)) =
      (M + r) * (M + r + 2) + ((r + 1 + s) ^ 2 * L + r * (r + 2 * s) + 2 * (r + 1 + s)) := by
    calc _ = (r + 1 + s) ^ 2 * (T + T) + 2 * (r + 1 + s) * ((L + 1) * (r + 1)) := by ring
      _ = (r + 1 + s) ^ 2 * (L * (L + 1)) + 2 * (r + 1 + s) * ((L + 1) * (r + 1)) := by
        rw [hT]
      _ = _ := by rw [← hM]; ring
  rw [hY]
  exact Nat.le_add_right _ _

/-- The exact first moment of `j ↦ j * (u - c * j)` over `range (J + 1)`, computed over `ℤ` so
that the subtraction is not truncated. -/
private lemma sum_range_mul_sub (u c J : ℕ) :
    6 * (∑ j ∈ range (J + 1), (j : ℤ) * (u - c * j))
      = 3 * u * J * (J + 1) - c * J * (J + 1) * (2 * J + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ]
      push_cast
      linear_combination ih

/-- Three-variable AM-GM, in the polynomial form needed for the first-moment bound.

The three hints are the Schur-shaped products `a * (b - c) ^ 2` and its cyclic images, which
already span the certificate. -/
private lemma mul_mul_le_cube {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  nlinarith [mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (a - c)),
    mul_nonneg hc (sq_nonneg (a - b))]

/-- Summing the `Y`-degree over the index set, one `Y`-degree at a time. -/
lemma sum_snd_weightBoundIndices_eq (D : ℕ) (hk : 1 < k) :
    (∑ p ∈ weightBoundIndices k D, p.2)
      = ∑ j ∈ range (D / (k - 1) + 1), j * (D - (k - 1) * j + 1) := by
  rw [weightBoundIndices_eq_filter_product D hk, Finset.sum_filter, product_eq_sprod,
    Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hcj : (k - 1) * j ≤ D := by
    have hj' : j ≤ D / (k - 1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc (k - 1) * j ≤ (k - 1) * (D / (k - 1)) := by gcongr
      _ ≤ D := Nat.mul_div_le D (k - 1)
  have hfilter : filter (fun i ↦ i + (k - 1) * j ≤ D) (range (D + 1))
      = range (D - (k - 1) * j + 1) := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, card_range, smul_eq_mul, mul_comm]

/-- The first-moment bound: the sum of the `Y`-degrees over the Guruswami-Sudan index set
`{(i, j) : i + (k-1) * j ≤ D}` is at most `(D + 1) ^ 3 / (6 * (k-1) ^ 2)`, stated
denominator-free.

This sum (called `D_C` in [BCIKS20]) controls the total `Y, Z`-degree of the interpolation
polynomial in the curve regime. The bound is essentially tight: for `k = 2` and `D = 4` the two
sides are `120` and `125`. -/
lemma sum_snd_weightBoundIndices_le (D : ℕ) (hk : 1 < k) :
    6 * (k - 1) ^ 2 * (∑ p ∈ weightBoundIndices k D, p.2) ≤ (D + 1) ^ 3 := by
  obtain ⟨κ, rfl⟩ : ∃ κ, k = κ + 1 := ⟨k - 1, by omega⟩
  have hκ0 : 0 < κ := by omega
  rw [sum_snd_weightBoundIndices_eq D hk]
  simp only [Nat.add_sub_cancel]
  set J := D / κ with hJdef
  set S := ∑ j ∈ range (J + 1), j * (D - κ * j + 1) with hSdef
  have hcj : ∀ j ∈ range (J + 1), κ * j ≤ D := by
    intro j hj
    have hj' : j ≤ D / κ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc κ * j ≤ κ * (D / κ) := by gcongr
      _ ≤ D := Nat.mul_div_le D κ
  have hcast : (S : ℤ) = ∑ j ∈ range (J + 1), (j : ℤ) * ((D : ℤ) + 1 - κ * j) := by
    rw [hSdef]
    push_cast
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Nat.cast_sub (hcj j hj)]
    push_cast
    ring
  have hexact : 6 * (S : ℤ)
      = 3 * ((D : ℤ) + 1) * J * (J + 1) - κ * J * (J + 1) * (2 * J + 1) := by
    rw [hcast]
    exact_mod_cast sum_range_mul_sub (D + 1) κ J
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ1
  · have h6 : 6 * (S : ℤ) = 0 := by rw [hexact, hJ0]; ring
    have : S = 0 := by omega
    rw [this, mul_zero]
    exact Nat.zero_le _
  · have hτD : κ * J ≤ D := by
      calc κ * J ≤ κ * (D / κ) := by gcongr
        _ ≤ D := Nat.mul_div_le D κ
    have hτ0 : (0 : ℤ) ≤ (κ : ℤ) * J := by positivity
    have hτu : (κ : ℤ) * J ≤ (D : ℤ) := by exact_mod_cast hτD
    have hκτ : (κ : ℤ) ≤ (κ : ℤ) * J := by
      exact_mod_cast Nat.le_mul_of_pos_right κ hJ1
    have hc0 : (0 : ℤ) ≤ 3 * ((D : ℤ) + 1) - 2 * ((κ : ℤ) * J) - κ := by
      linarith only [hτu, hκτ]
    have hkey : 6 * (κ : ℤ) ^ 2 * S
        = ((κ : ℤ) * J) * ((κ : ℤ) * J + κ)
          * (3 * ((D : ℤ) + 1) - 2 * ((κ : ℤ) * J) - κ) := by
      linear_combination (κ : ℤ) ^ 2 * hexact
    have hamgm := mul_mul_le_cube hτ0 (by positivity : (0 : ℤ) ≤ (κ : ℤ) * J + κ) hc0
    have hsum : (κ : ℤ) * J + ((κ : ℤ) * J + κ)
        + (3 * ((D : ℤ) + 1) - 2 * ((κ : ℤ) * J) - κ) = 3 * ((D : ℤ) + 1) := by ring
    rw [hsum] at hamgm
    have hfinal : 6 * (κ : ℤ) ^ 2 * S ≤ ((D : ℤ) + 1) ^ 3 := by
      rw [hkey]; linarith only [hamgm]
    exact_mod_cast hfinal

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
  have h_eq : (constraintIndices m).card = ∑ s ∈ range m, (m - s) := by
    rw [show constraintIndices m = (range m).biUnion fun s ↦
      (range (m - s)).image (fun t ↦ (s, t)) from ?_, card_biUnion]
    · exact sum_congr rfl fun s _ ↦ (card_image_of_injective _ fun _ _ h ↦
        (Prod.ext_iff.mp h).2).trans (card_range _)
    · exact fun i _ j _ hij ↦ disjoint_left.mpr fun x hx₁ hx₂ ↦ by
        obtain ⟨t, -, rfl⟩ := mem_image.mp hx₁
        obtain ⟨t', -, h⟩ := mem_image.mp hx₂
        exact hij (congrArg Prod.fst h).symm
    · ext ⟨s, t⟩
      simp only [constraintIndices, product_eq_sprod, mem_filter, mem_product, mem_range,
        mem_biUnion, mem_image, Prod.mk.injEq, exists_eq_right_right]
      omega
  have h_reflect : ∑ s ∈ range m, (m - s) = ∑ s ∈ range (m + 1), s := by
    rw [sum_range_succ', add_zero, ← sum_range_reflect]
    exact sum_congr rfl fun j hj ↦ by have := mem_range.mp hj; omega
  rw [h_eq, h_reflect, sum_range_id, Nat.add_sub_cancel, mul_comm]

end numConstraints

section numVars_gt_numConstraints

/-- The floor bound `⌊(m + 1/2) * √(a/n) * n⌋₊` behind both degree bounds satisfies
`(⌊…⌋₊ + 1)^2 > (m + 1/2)^2 * a * n`. -/
private lemma floor_sqrt_bound_sq_gt (a : ℚ) (ha : 0 ≤ a) (hn : n ≠ 0) :
    ((⌊(m + 1 / 2) * √(a / n : ℚ) * n⌋₊ : ℝ) + 1) ^ 2 > (m + 1 / 2) ^ 2 * a * n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsq : ((m + 1 / 2 : ℝ) * √(a / n : ℚ) * n) ^ 2 = (m + 1 / 2) ^ 2 * a * n := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Rat.cast_nonneg.mpr (div_nonneg ha n.cast_nonneg))]
    push_cast
    field_simp
  rw [gt_iff_lt, ← hsq]
  exact pow_lt_pow_left₀ (Nat.lt_floor_add_one _) (by positivity) two_ne_zero

/-- Lower bound for the square of (D+1). Specifically, (D+1)^2 > (m+1/2)^2 * (k+1) * n. -/
lemma proximity_gap_degree_bound_sq_gt (hn : n ≠ 0) :
    ((proximity_gap_degree_bound k n m : ℝ) + 1) ^ 2 >
      (m + 1 / 2) ^ 2 * (k + 1) * n := by
  have := floor_sqrt_bound_sq_gt (m := m) ((k : ℚ) + 1) (by positivity) hn
  rw [Rat.cast_add, Rat.cast_natCast, Rat.cast_one] at this
  exact this

/-- The Guruswami-Sudan counting bound, stated for an arbitrary degree bound `D`: the system is
underdetermined as soon as `D * (D + 2) > (k - 1) * n * m * (m + 1)`.

This is the shared core of the counting arguments; a concrete degree bound only has to supply the
displayed inequality, which for the usual choices follows from a lower bound on `(D + 1) ^ 2`. -/
lemma numVars_gt_numConstraints_of_mul_lt {D : ℕ} (hk : 1 < k)
    (h : ((k : ℝ) - 1) * n * m * (m + 1) < (D : ℝ) * (D + 2)) :
    numVars k D > numConstraints n m := by
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk.le, Nat.cast_one]
  rw [← hc] at h
  have h' : (k - 1) * n * m * (m + 1) < D * (D + 2) := by exact_mod_cast h
  have h2 : (k - 1) * (n * (m * (m + 1))) < (k - 1) * (2 * numVars k D) :=
    calc (k - 1) * (n * (m * (m + 1))) = (k - 1) * n * m * (m + 1) := by ring
      _ < D * (D + 2) := h'
      _ ≤ 2 * (k - 1) * numVars k D := numVars_lower_bound_tight hk
      _ = (k - 1) * (2 * numVars k D) := by ring
  rw [gt_iff_lt, numConstraints, card_constraintIndices]
  exact (Nat.mul_div_le_mul_div_assoc _ _ _).trans_lt
    (Nat.div_lt_of_lt_mul (Nat.lt_of_mul_lt_mul_left h2))

private lemma one_le_n_mul_m_mul_succ (hn : n ≠ 0) (hm : 1 ≤ m) :
    (1 : ℝ) ≤ n * m * (m + 1) :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn))
      (Nat.one_le_cast.mpr hm))
    (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])

lemma numVars_gt_numConstraints_of_gt_one (hn : n ≠ 0) (hk : 1 < k) (hm : 1 ≤ m) :
    numVars k (proximity_gap_degree_bound k n m) > numConstraints n m := by
  have hD := proximity_gap_degree_bound_sq_gt (k := k) (m := m) hn
  refine numVars_gt_numConstraints_of_mul_lt hk ?_
  have hnm := one_le_n_mul_m_mul_succ (m := m) hn hm
  linarith [(by positivity : (0 : ℝ) ≤ k * n)]

lemma numVars_gt_numConstraints (k n m : ℕ) :
    numVars k (proximity_gap_degree_bound k n m) > numConstraints n m := by
  by_cases hk : k ≤ 1
  · rw [numVars_eq_sq hk, numConstraints, card_constraintIndices]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [zero_mul]; positivity
    · have hsq := proximity_gap_degree_bound_sq_gt (k := k) (m := m) hn.ne'
      generalize proximity_gap_degree_bound k n m = D at hsq ⊢
      have h2 : n * (m * (m + 1) / 2) * 2 ≤ n * (m * (m + 1)) := by
        rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      have hreal : ((n * (m * (m + 1)) : ℕ) : ℝ) < ((2 * (D + 1) ^ 2 : ℕ) : ℝ) := by
        push_cast
        linarith [mul_nonneg (mul_nonneg (sq_nonneg ((m : ℝ) + 1 / 2)) (Nat.cast_nonneg k))
            (Nat.cast_nonneg n), mul_nonneg (sq_nonneg (m : ℝ)) (Nat.cast_nonneg n),
          mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) n),
          (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have := Nat.cast_lt.mp hreal
      omega
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
noncomputable def coeffsToPoly (k D : ℕ) : ((weightBoundIndices k D) → F) →ₗ[F] F[X][Y] :=
  linearCombination F (fun p : weightBoundIndices k D ↦ monomial p.1.1 p.1.2) ∘ₗ
    (linearEquivFunOnFinite F F (weightBoundIndices k D)).symm.toLinearMap

/-- The linear map evaluating the (s,t)-th derivative coefficient at (x,y). -/
noncomputable def evalConstraint (x y : F) (s t : ℕ) : F[X][Y] →ₗ[F] F where
  toFun f := ((shift f x y).coeff t).coeff s
  map_add' f g := by simp [shift]
  map_smul' a f := by simp [shift]

/-- The linear map representing the system of linear equations. -/
noncomputable def constraintMap (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) (D : ℕ) :
  ((weightBoundIndices k D) → F) →ₗ[F] (Fin n → constraintIndices m → F) where
  toFun c i st := evalConstraint (ωs i) (f i) st.1.1 st.1.2 (coeffsToPoly k D c)
  map_add' c d := by simp +zetaDelta at *; rfl
  map_smul' a c := by unfold evalConstraint coeffsToPoly; aesop

/-- A dimension surplus gives a nonzero coefficient vector in the constraint map's kernel. -/
private lemma exists_nonzero_solution_of_numVars_gt (k n m : ℕ) (ωs : Fin n ↪ F)
    (f : Fin n → F) (D : ℕ) (hD : numVars k D > numConstraints n m) :
    ∃ c : (weightBoundIndices k D) → F, c ≠ 0 ∧ constraintMap k n m ωs f D c = 0 := by
  have h_kernel_nontrivial : Module.finrank F ((weightBoundIndices k D) → F) >
      Module.finrank F ((Fin n → constraintIndices m → F)) := by
    convert hD using 1
    · simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, numVars]
    · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Module.finrank_fintype_fun_eq_card, Fintype.card_coe, smul_eq_mul]
      rfl
  have h_inj : ¬ Function.Injective (constraintMap k n m ωs f D) := by
    intro h_inj
    exact h_kernel_nontrivial.not_ge
      (LinearMap.finrank_range_of_inj h_inj ▸ Submodule.finrank_le _)
  contrapose! h_inj
  exact LinearMap.ker_eq_bot.mp (eq_bot_iff.mpr fun x hx ↦
    by_contra fun hx' ↦ h_inj x hx' (LinearMap.mem_ker.mp hx))

/-- There exists a non-zero polynomial satisfying the conditions. -/
lemma exists_nonzero_solution (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    ∃ c : (weightBoundIndices k (proximity_gap_degree_bound k n m)) → F,
    c ≠ 0 ∧ constraintMap k n m ωs f (proximity_gap_degree_bound k n m) c = 0 :=
  exists_nonzero_solution_of_numVars_gt k n m ωs f _ (numVars_gt_numConstraints k n m)

/-- Generalized existence: non-zero kernel element for arbitrary degree bound D,
    given numVars k D > numConstraints n m. -/
lemma exists_nonzero_solution_gen (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) (D : ℕ)
    (hD : numVars k D > numConstraints n m) :
    ∃ c : (weightBoundIndices k D) → F,
    c ≠ 0 ∧ constraintMap k n m ωs f D c = 0 :=
  exists_nonzero_solution_of_numVars_gt k n m ωs f D hD

/-- The polynomial solution constructed from the non-zero kernel element. -/
noncomputable def polySol (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : F[X][Y] :=
  let c := Classical.choose (exists_nonzero_solution k n m ωs f)
  coeffsToPoly k (proximity_gap_degree_bound k n m) c

/-- Polynomial solution with rate-corrected degree bound (ρ = k/n). -/
noncomputable def gs_polySol (k n m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (hD : numVars k (gs_degree_bound k n m) > numConstraints n m) : F[X][Y] :=
  let c := Classical.choose (exists_nonzero_solution_gen k n m ωs f (gs_degree_bound k n m) hD)
  coeffsToPoly k (gs_degree_bound k n m) c

end solution

section neZero

/-- The coefficient of X^i Y^j in a linear combination of monomials is the coefficient
    of the combination. -/
lemma coeff_linearCombination_monomial (c : ℕ × ℕ →₀ F) (i j : ℕ) :
    ((linearCombination F (fun p ↦ monomial (F := F) p.1 p.2) c).coeff j).coeff i = c (i, j) := by
    simp only [linearCombination_apply, Finsupp.sum, finsetSum_coeff, coeff_smul, smul_eq_mul]
    rw [Finset.sum_eq_single (i, j)] <;> simp +contextual only [Finsupp.mem_support_iff, ne_eq,
      mul_eq_zero, false_or, Prod.forall, Prod.mk.injEq, not_and]
    · erw [coeff_monomial, ite_eq_left rfl]; aesop
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
    have hc := congr_arg (fun f ↦ (f.coeff j).coeff i) hl
    rw [coeff_linearCombination_monomial] at hc
    simpa using hc

/-- The solved polynomial is non-zero. -/
lemma polySol_ne_zero :
    polySol k n m ωs f ≠ 0 := by
    have := Classical.choose_spec (exists_nonzero_solution k n m ωs f)
    have h_inj : Function.Injective (coeffsToPoly (F := F) k
    (proximity_gap_degree_bound k n m)) := by
      have : Function.Injective (linearCombination F
        (fun p : weightBoundIndices k (proximity_gap_degree_bound k n m) ↦
          monomial (F := F) p.1.1 p.1.2)) :=
        linearIndependent_monomials.comp _ (fun _ _ h ↦ Subtype.ext h)
      exact this.comp (LinearEquiv.injective _)
    exact fun h ↦ this.1 <| h_inj <| h.trans (map_zero _).symm

end neZero

section weightedDegree

/-- The weighted degree of a monomial X^i Y^j is u*i + v*j. -/
lemma natWeightedDegree_monomial (i j u v : ℕ) :
    natWeightedDegree (monomial (F := F) i j) u v = u * i + v * j := by
    classical
    simp only [natWeightedDegree, monomial]
    refine le_antisymm ?_ ?_ <;> norm_num [coeff_monomial]

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
lemma natWeightedDegree_coeffsToPoly_le (k D : ℕ) (c : (weightBoundIndices k D) → F) :
    natWeightedDegree (coeffsToPoly k D c) 1 (k - 1) ≤ D := by
  have h : coeffsToPoly k D c =
      ∑ p : weightBoundIndices k D, c p • monomial (F := F) p.1.1 p.1.2 := by
    simp only [coeffsToPoly, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      linearCombination_apply, zero_smul, implies_true, sum_fintype, univ_eq_attach,
      linearEquivFunOnFinite_symm_apply]
  rw [h]
  refine (natWeightedDegree_sum_le _ _ _ _).trans (Finset.sup_le fun p _ ↦ ?_)
  refine (natWeightedDegree_smul_le _ _ _ _).trans ?_
  rw [natWeightedDegree_monomial_eq, one_mul]
  exact (mem_filter.mp p.2).2

/-- The solved polynomial has weighted degree at most the proximity gap degree bound. -/
lemma polySol_weightedDegree_le :
    weightedDegree (polySol k n m ωs f) 1 (k - 1) ≤
    proximity_gap_degree_bound k n m := by
  convert Option.some_le_some.mpr
    (natWeightedDegree_coeffsToPoly_le k (proximity_gap_degree_bound k n m)
    (Classical.choose (exists_nonzero_solution k n m ωs f))) using 1
  exact weightedDegree_eq_natWeightedDegree

theorem natDegree_le_of_natWeightedDegree {F : Type} [Field F]
    {Q : F[X][Y]} {b D : ℕ} (hb : 0 < b)
    (hwd : natWeightedDegree Q 1 b ≤ D) :
    Q.natDegree ≤ D / b := by
  by_cases hQ : Q = 0
  · simp [hQ]
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    by_contra h
    have hmem : j ∈ Q.support := Polynomial.mem_support_iff.mpr h
    have hle : 1 * (Q.coeff j).natDegree + b * j ≤ D :=
      le_trans (Finset.le_sup (f := fun m => 1 * (Q.coeff m).natDegree + b * m) hmem) hwd
    have : j ≤ D / b := Nat.le_div_iff_mul_le hb |>.mpr (by linarith)
    omega

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
    of `Q` at `(x, y)` is some `μ ≤ s + t`. -/
private lemma exists_rootMultiplicity_eq_some_le [DecidableEq F] {Q : F[X][Y]} {x y : F}
    {s t : ℕ} (h : Bivariate.coeff (shift Q x y) s t ≠ 0) :
    ∃ μ, rootMultiplicity Q x y = some μ ∧ μ ≤ s + t := by
  set g : F[X][Y] := shift Q x y
  have h_rootMultiplicity : Polynomial.Bivariate.rootMultiplicity Q x y =
      List.min? (List.filterMap (fun p ↦
        if Bivariate.coeff g p.1 p.2 = 0 then none
        else some (p.1 + p.2)) (List.product (List.range
          (natWeightedDegree g 1 1 + 1)) (List.range (natWeightedDegree g 1 1 + 1)))) := by
    rw [Bivariate.rootMultiplicity, Bivariate.rootMultiplicity₀,
      Bivariate.weightedDegree_eq_natWeightedDegree]
  have h_deg : s + t ≤ Bivariate.natWeightedDegree g 1 1 := by
    refine Finset.le_sup (f := fun m ↦ 1 * ((g.coeff m).natDegree ) + 1 * m)
        (Finset.mem_coe.mpr <| Polynomial.mem_support_iff.mpr <|
          show g.coeff t ≠ 0 from ?_) |> le_trans ?_
    · rw [one_mul, one_mul, add_le_add_iff_right]
      exact le_natDegree_of_ne_zero h
    · exact fun h' ↦ h <| by rw [Polynomial.Bivariate.coeff, h', Polynomial.coeff_zero]
  have hmem : s + t ∈ List.filterMap (fun p ↦ if Bivariate.coeff g p.1 p.2 = 0
      then Option.none else Option.some (p.1 + p.2)) (List.product (List.range
        (natWeightedDegree g 1 1 + 1)) (List.range (natWeightedDegree g 1 1 + 1))) :=
    List.mem_filterMap.mpr ⟨(s, t), List.mem_product.mpr ⟨List.mem_range.mpr (by omega),
      List.mem_range.mpr (by omega)⟩, by simp only [ite_eq_right h]⟩
  obtain ⟨μ, hμ⟩ := Option.isSome_iff_exists.mp (List.isSome_min?_of_mem hmem)
  exact ⟨μ, h_rootMultiplicity.trans hμ, list_min_le_of_mem hμ hmem⟩

/-- If the `(s, t)`-coefficient of `shift Q x y` is non-zero, then the root multiplicity
    of `Q` at `(x, y)` is at most `s + t`. -/
lemma rootMultiplicity_le_of_coeff_ne_zero [DecidableEq F] {Q : F[X][Y]} {x y : F} {s t : ℕ}
    (h : Bivariate.coeff (shift Q x y) s t ≠ 0) :
    rootMultiplicity Q x y ≤ (s + t : WithTop ℕ) := by
  obtain ⟨μ, hμ, hle⟩ := exists_rootMultiplicity_eq_some_le h
  rw [hμ]
  exact_mod_cast hle

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
  obtain ⟨s, t, hst⟩ : ∃ s t, Bivariate.coeff (shift f x y) s t ≠ 0 := by
    by_contra! H
    exact hf ((shift_eq_zero_iff f x y).1 (Polynomial.ext fun t ↦ Polynomial.ext fun s ↦ H s t))
  obtain ⟨μ, hμ, -⟩ := exists_rootMultiplicity_eq_some_le hst
  rw [hμ]
  exact Option.some_le_some.mpr ((rootMultiplicity₀_ge_iff _ m).1 h μ hμ)

lemma polySol_multiplicity [DecidableEq F] (i : Fin n) :
    m ≤ rootMultiplicity (polySol k n m ωs f) (ωs i) (f i) :=
  rootMultiplicity_ge_of_shift_zero polySol_ne_zero fun s t hst ↦
    congr_fun (congr_fun (Classical.choose_spec (exists_nonzero_solution k n m ωs f)).2 i)
      ⟨(s, t), mem_filter.2 ⟨mem_product.mpr ⟨mem_range.2 (by omega), mem_range.2 (by omega)⟩,
        hst⟩⟩

end multiplicity

section divisibility

open ReedSolomon

/-- The degree of Q(X, P(X)) is bounded by the (1, k-1)-weighted degree of Q,
    provided deg(P) ≤ k - 1. -/
lemma degree_eval_le_weightedDegree (Q : F[X][Y]) (P : F[X]) (k : ℕ) (hP : P.natDegree ≤ k - 1) :
    (Q.eval P).natDegree ≤ natWeightedDegree Q 1 (k - 1) := by
  have h_deg_Q : (Q.eval P).natDegree ≤
      (Q.support.image (fun m => (Q.coeff m).natDegree + (k - 1) * m)).sup id := by
    rw [Polynomial.eval_eq_sum_range]
    refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le ?_)
    intro i hi; by_cases hi' : Q.coeff i = 0 <;> simp_all only [mem_range, Function.comp_apply,
      zero_mul, natDegree_zero, sup_image, CompTriple.comp_eq, zero_le]
    refine le_trans ?_ (Finset.le_sup
      (f := fun m ↦ (Q.coeff m).natDegree + (k - 1) * m) (show i ∈ Q.support from ?_))
    · exact (Polynomial.natDegree_mul_le ..).trans (Nat.add_le_add_left
        (natDegree_pow_le.trans ((Nat.mul_le_mul_left i hP).trans_eq (mul_comm _ _))) _)
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
    by_contra hR
    have h_factor : ∏ x ∈ A.image (fun i ↦ ωs i), (X - C x) ^ (R.rootMultiplicity x) ∣ R := by
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intros x hx y hy hxy
        exact IsCoprime.pow ((irreducible_X_sub_C x).coprime_iff_not_dvd.mpr
          fun h' ↦ hxy (root_X_sub_C.mp (dvd_iff_isRoot.mp h')).symm)
      · exact fun x hx ↦ R.pow_rootMultiplicity_dvd x
    have h_sum_multiplicities :
        ∑ x ∈ A.image (fun i ↦ ωs i), (R.rootMultiplicity x) ≤ R.natDegree := by
      have := natDegree_le_of_dvd h_factor hR
      rwa [natDegree_prod_of_monic _ _ fun x _ ↦ (monic_X_sub_C x).pow _,
        Finset.sum_congr rfl fun x _ ↦ by rw [natDegree_pow, natDegree_X_sub_C, mul_one]]
        at this
    rw [Finset.sum_image fun i _ j _ h ↦ ωs.injective h] at h_sum_multiplicities
    refine h_deg.not_ge <| h_sum_multiplicities.trans' ?_
    rw [mul_comm, ← smul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ h_roots

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
      rw [eval_finsetSum, Finset.sum_eq_single i]
      · rw [eval_mul, Lagrange.eval_basis_self (by exact ωs.injective.injOn) (mem_univ i)]
        norm_num
      all_goals aesop

/-- The polynomial corresponding to a codeword has degree at most k-1. -/
lemma toPolynomial_degree_le (hk : k + 1 ≤ n) (p : code ωs k) :
    (toPolynomial p).natDegree ≤ k - 1 := by
    rw [toPolynomial_def]
    obtain ⟨q, hq, hp⟩ := p.2
    have h_interpolate : (Lagrange.interpolate Finset.univ ωs.toFun) (evalOnPoints ωs q) = q := by
      simpa [evalOnPoints, Function.Embedding.toFun_eq_coe] using
        interpolate_eq_of_degree_lt q
          (lt_of_le_of_lt (natDegree_le_of_degree_le <| mem_degreeLT.mp hq |> le_of_lt) hk)
    rcases k <;> simp_all only [Function.Embedding.toFun_eq_coe, Lagrange.interpolate_apply,
      zero_add, degreeLT, ge_iff_le, zero_le, iInf_pos, Submodule.coe_iInf, Set.mem_iInter,
      SetLike.mem_coe, LinearMap.mem_ker, lcoeff_apply, zero_tsub, nonpos_iff_eq_zero]
    · rw [show q = 0 from Polynomial.ext hq]; norm_num
    · exact natDegree_le_iff_coeff_eq_zero.mpr hq

/-- The floor bound `⌊(m + 1/2) * √(a/n) * n⌋₊` behind both degree bounds is below
`m * (n - dist)` whenever `dist / n` is below the matching Johnson radius. -/
private lemma floor_sqrt_bound_lt_of_lt_johnson {a : ℚ} {dist : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (h_dist : (dist : ℝ) / n < 1 - √(a / n : ℚ) - √(a / n : ℚ) / (2 * m)) :
    (⌊(m + 1 / 2) * √(a / n : ℚ) * n⌋₊ : ℝ) < m * (n - dist) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [div_lt_iff₀ hn'] at h_dist
  refine (Nat.floor_le (by positivity)).trans_lt ?_
  set r := √(a / n : ℚ)
  have h : (m + 1 / 2 : ℝ) * r * n = m * ((r + r / (2 * m)) * n) := by
    field_simp
  rw [h]
  refine mul_lt_mul_of_pos_left ?_ hm'
  linear_combination h_dist

/-- The degree bound is strictly less than `m` times the number of agreement points,
    provided the distance is within the Johnson radius. -/
lemma sufficient_multiplicity_bound {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (h_dist : (dist : ℝ) / n < proximity_gap_johnson k n m) :
  (proximity_gap_degree_bound k n m : ℝ) < m * (n - dist) :=
  floor_sqrt_bound_lt_of_lt_johnson (by omega) hm h_dist

private theorem dvd_property_of_sufficient_multiplicity_bound [DecidableEq F]
    (hk : k + 1 ≤ n) (p : code ωs k) {D : ℕ} {radius : ℝ} {Q : F[X][Y]}
    (hQ_deg : weightedDegree Q 1 (k - 1) ≤ D)
    (hQ_mult : ∀ i, m ≤ rootMultiplicity Q (ωs i) (f i))
    (h_dist : (hammingDist f (fun i ↦ (toPolynomial p).eval (ωs i)) : ℝ) / n < radius)
    (hsufficient : ∀ {dist : ℕ}, (dist : ℝ) / n < radius → (D : ℝ) < m * (n - dist)) :
    X - C (toPolynomial p) ∣ Q := by
  contrapose! h_dist with h_distots
  have hR_nonzero : (Q.eval (toPolynomial p)) ≠ 0 := by
    contrapose! h_distots
    exact dvd_iff_isRoot.mpr h_distots
  have hR_roots : (Q.eval (toPolynomial p)).natDegree ≥
      m * (n - hammingDist f (fun i ↦ (toPolynomial p).eval (ωs i))) := by
    have hR_roots : ∀ i ∈ Finset.univ.filter (fun i ↦ f i = (toPolynomial p).eval (ωs i)), m ≤
        (Q.eval (toPolynomial p)).rootMultiplicity (ωs i) := by
      intro i hi
      have h_root : m ≤ (Q.eval (toPolynomial p)).rootMultiplicity (ωs i) := by
        have hQ_mult : HasOrderAt Q (ωs i) (f i) m :=
          (rootMultiplicity₀_ge_iff _ m).2 fun r hr ↦
            Option.some_le_some.mp (Option.mem_def.mp hr ▸ hQ_mult i)
        rw [(Finset.mem_filter.mp hi).2] at hQ_mult
        exact (orderAt_eval_ge Q (toPolynomial p) (ωs i) m hQ_mult).resolve_left hR_nonzero
      exact h_root
    have hR_roots_card : (Finset.univ.filter (fun i ↦
        f i = (toPolynomial p).eval (ωs i))).card * m ≤
          (Q.eval (toPolynomial p)).natDegree := by
      have hR_roots_card : (∏ i ∈ Finset.univ.filter (fun i ↦
          f i = (toPolynomial p).eval (ωs i)), (X - C (ωs i)) ^ m) ∣
            (Q.eval (toPolynomial p)) := by
        refine Finset.prod_dvd_of_coprime ?_ ?_
        · intros i hi j hj hij
          exact IsCoprime.pow ((irreducible_X_sub_C (ωs i)).coprime_iff_not_dvd.mpr
            fun h ↦ hij (ωs.injective (root_X_sub_C.mp (dvd_iff_isRoot.mp h))).symm)
        · exact fun i hi ↦
            dvd_trans (pow_dvd_pow _ (hR_roots i hi)) (pow_rootMultiplicity_dvd _ _)
      have := natDegree_le_of_dvd hR_roots_card hR_nonzero
      rwa [natDegree_prod_of_monic _ _ fun i _ ↦ (monic_X_sub_C _).pow _,
        Finset.sum_congr rfl fun i _ ↦ by rw [natDegree_pow, natDegree_X_sub_C, mul_one],
        Finset.sum_const, smul_eq_mul] at this
    convert hR_roots_card.ge using 1
    simp only [hammingDist, ne_eq, mul_comm, mul_eq_mul_left_iff]
    rw [Finset.filter_not, Finset.card_sdiff]
    norm_num
    exact Or.inl (Nat.sub_sub_self (le_trans (Finset.card_le_univ _) (by norm_num)))
  have hR_deg : (Q.eval (toPolynomial p)).natDegree ≤ D := by
    have hR_deg : (Q.eval (toPolynomial p)).natDegree ≤ natWeightedDegree Q 1 (k - 1) := by
      apply degree_eval_le_weightedDegree
      exact toPolynomial_degree_le hk p
    rw [weightedDegree_eq_natWeightedDegree] at hQ_deg
    exact hR_deg.trans (Option.some_le_some.mp hQ_deg)
  contrapose! hR_roots
  refine lt_of_le_of_lt hR_deg ?_
  convert hsufficient hR_roots using 1
  rw [← @Nat.cast_lt ℝ]
  norm_num [Nat.cast_sub (show hammingDist f (fun i ↦ (toPolynomial p).eval (ωs i)) ≤ n
    from le_trans (Finset.card_le_univ _) (by norm_num))]

/-- If $Q$ satisfies the weighted degree bound and vanishes to order $m$ at each point
    $(\omega_i, f_i)$, and if $P$ is a codeword close enough to $f$, then $Y - P(X)$
    divides $Q(X,Y)$. -/
theorem dvd_property [DecidableEq F] (hk : k + 1 ≤ n) (hm : 1 ≤ m) (p : code ωs k)
    {Q : F[X][Y]}
  (hQ_deg : weightedDegree Q 1 (k - 1) ≤ proximity_gap_degree_bound k n m)
  (hQ_mult : ∀ i, m ≤ rootMultiplicity Q (ωs i) (f i))
  (h_dist : (hammingDist f (fun i ↦ (toPolynomial p).eval (ωs i)) : ℝ) / n <
    proximity_gap_johnson k n m) :
  X - C (toPolynomial p) ∣ Q := by
  exact dvd_property_of_sufficient_multiplicity_bound hk p hQ_deg hQ_mult h_dist
    (sufficient_multiplicity_bound hk hm)

end divisibility

section gs_rate

open ReedSolomon

/-- Lower bound: (gs_degree_bound + 1)^2 > (m+1/2)^2 * k * n. -/
lemma gs_degree_bound_sq_gt (hn : n ≠ 0) (hk : 0 < k) :
    ((gs_degree_bound k n m : ℝ) + 1) ^ 2 > (m + 1 / 2) ^ 2 * k * n := by
  have := floor_sqrt_bound_sq_gt (m := m) (k : ℚ) (Nat.cast_pos.mpr hk).le hn
  rw [Rat.cast_natCast] at this
  exact this

/-- numVars with gs_degree_bound exceeds numConstraints (for k > 1). -/
lemma gs_numVars_gt_numConstraints_of_gt_one (hn : n ≠ 0) (hk : 1 < k) (hm : 1 ≤ m) :
    numVars k (gs_degree_bound k n m) > numConstraints n m := by
  have hD := gs_degree_bound_sq_gt (m := m) hn (by omega : 0 < k)
  refine numVars_gt_numConstraints_of_mul_lt hk ?_
  have hnm := one_le_n_mul_m_mul_succ (m := m) hn hm
  linarith [(by positivity : (0 : ℝ) ≤ k * n)]

/-- The degree bound with ρ = k/n is strictly less than m times the number of
    agreement points, provided the distance is within the rate-corrected Johnson
    radius gs_johnson. -/
lemma gs_sufficient_multiplicity_bound {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (h_dist : (dist : ℝ) / n < gs_johnson k n m) :
  (gs_degree_bound k n m : ℝ) < m * (n - dist) :=
  floor_sqrt_bound_lt_of_lt_johnson (by omega) hm h_dist

/-- Divisibility via the rate-corrected GS system. Uses gs_degree_bound (ρ=k/n)
    and gs_johnson instead of the conservative proximity_gap versions. -/
theorem gs_dvd_property [DecidableEq F] (hk : k + 1 ≤ n) (hm : 1 ≤ m) (p : code ωs k)
    {Q : F[X][Y]}
  (hQ_deg : weightedDegree Q 1 (k - 1) ≤ gs_degree_bound k n m)
  (hQ_mult : ∀ i, m ≤ rootMultiplicity Q (ωs i) (f i))
  (h_dist : (hammingDist f (fun i ↦ (toPolynomial p).eval (ωs i)) : ℝ) / n <
    gs_johnson k n m) :
  X - C (toPolynomial p) ∣ Q := by
  exact dvd_property_of_sufficient_multiplicity_bound hk p hQ_deg hQ_mult h_dist
    (gs_sufficient_multiplicity_bound hk hm)


end gs_rate

end GuruswamiSudan

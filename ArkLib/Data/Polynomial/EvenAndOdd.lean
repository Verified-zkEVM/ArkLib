/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
import ArkLib.ToMathlib.Finset.Basic
import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.FoldingPolynomial

import CompPoly.Fields.Basic

/-!
# Even and odd parts of polynomial

The FFT-style splitting of a polynomial `f` of degree `n` into two polynomials
`evenPart` and `oddPart` of degree `< n/2` such that `f = evenPart + X * oddPart`.

This is the special case `n = 2` of the generalized n-way splitting defined in
`Polynomial/SplitFold.lean`. The formal connection between the two will be
established in future PRs.

## Main definitions

* `evenPart f`: Extracts the even-powered terms of `f`
* `oddPart f`: Extracts the odd-powered terms of `f` (divided by X)
* `evenPart_x f`, `oddPart_x f`: The above with substitution `X² ↦ X` applied

-/

namespace Polynomial

variable {F : Type*} [NonBinaryField F]

/-- The even part of a polynomial `f = a_0 + a_1 X + a_2 X² + ...`, which is the polynomial

  `(f(X) + f(-X)) / 2 = a_0 + a_2 X² + a_4 X⁴ + ...`.

  Note that the exponents are not divided by `2`.
-/
noncomputable def evenPart (f : Polynomial F) : Polynomial F :=
    C (2⁻¹ : F) * (f + f.comp (-X))

/-- The odd part of a polynomial `f = a_0 + a_1 X + a_2 X² + ...`, which is the polynomial

  `(f(X) - f(-X)) / (2X) = a_1 + a_3 X² + a_5 X⁴ + ...`.

  Note that the exponents are not divided by `2`.
-/
noncomputable def oddPart (f : Polynomial F) : Polynomial F :=
    C (2⁻¹ : F) * (f - f.comp (-X)) /ₘ X

section

variable {f : Polynomial F}

lemma evenPart_def :
  evenPart f = C (2⁻¹ : F) * (f + f.comp (-X)) := rfl

@[simp]
lemma evenPart_by_2 :
  2 * (evenPart f) = f + f.comp (-X) := by
  simp [evenPart_def, ext_iff]

lemma oddPart_def :
  oddPart f =
  C (2⁻¹ : F) * (f - f.comp (-X)) /ₘ X
  := rfl

@[simp]
lemma oddPart_by_2 :
    2 * (oddPart f) = (f - f.comp (-X)) /ₘ X
 := by
  simp [oddPart_def, ext_iff]
  by_cases heq : f - f.comp (-X) = 0
  · simp [heq]
  · intro n
    rw [show X = X - C (0 : F) by simp
    , coeff_divByMonic_X_sub_C
    , coeff_divByMonic_X_sub_C
    , Finset.mul_sum]
    apply Finset.sum_bij (fun n _ => n) <;> aesop (add simp natDegree_mul, safe (by field_simp))
end

/-- A polynomial is even if does not contain
  odd terms.
-/
def EvenPoly (f : Polynomial F) : Prop := ∀ n, Odd n → f.coeff n = 0

lemma even_poly_has_even_degree {f : F[X]}
  (h : f.EvenPoly)
  :
  Even f.natDegree
  := by
  simp only [EvenPoly] at h
  by_contra contra
  rw [Nat.not_even_iff_odd] at contra
  specialize h _ contra
  simp only [coeff_natDegree, leadingCoeff_eq_zero] at h
  rw [h] at contra
  simp at contra

/-- Given a polynomial `f`, `deevenize` removes
  all the odd terms and substitutes `X² ↦ X`.
-/
noncomputable def deevenize (f : Polynomial F) : Polynomial F :=
    match f with
      | ⟨⟨supp, g, h⟩⟩ => ⟨⟨divide_by_2 supp, fun n => g (2 * n), by
        aesop
      ⟩⟩

@[simp]
lemma deevenize_zero :
  deevenize 0 = (0 : F[X]) := by rfl

@[simp]
lemma deevenize_coeff {f : Polynomial F} {n : ℕ} :
    (deevenize f).coeff n = f.coeff (2 * n) := by aesop (add simp deevenize)

/-- Given a polynomial `f`, `evenize`
  substitutes `X ↦ X²`.
-/
noncomputable def evenize (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, g, h⟩⟩ => ⟨⟨mul_by_2 supp, fun n => if Even n then g (n / 2) else 0, by
    aesop
  ⟩⟩

@[simp]
lemma evenize_coeff {f : Polynomial F} {n : ℕ} :
    (evenize f).coeff n = if Even n then f.coeff (n / 2) else 0 := by aesop (add simp evenize)

/-- `evenPart` with the substitution `X² ↦ X` applied.
-/
noncomputable def evenPart_x (f : Polynomial F) : Polynomial F := deevenize (evenPart f)
/-- `oddPart` with the substitution `X² ↦ X` applied.
-/
noncomputable def oddPart_x (f : Polynomial F) : Polynomial F := deevenize (oddPart f)

-- Merged the `Lemmas` files into here
section Lemmas

variable {F : Type*} [NonBinaryField F]

private noncomputable def evenPart' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨erase_odd supp, fun n => if Even n then f n else 0, by {
    intro a
    aesop
  }⟩⟩

@[simp]
private lemma evenPart'_coeffs {f : Polynomial F} {n : ℕ} :
    (evenPart' f).coeff n = if Even n then f.coeff n else 0 := by
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp [evenPart']

private noncomputable def x_times_oddPart' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨erase_even supp, fun n => if Odd n then f n else 0, by {
      intro a
      aesop
    }⟩⟩

@[simp]
private lemma x_times_oddPart'_coeff {f : Polynomial F} {n : ℕ} :
    (x_times_oddPart' f).coeff n = if Odd n then f.coeff n else 0 := by
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp [x_times_oddPart']

private noncomputable def oddPart' (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, f, pr⟩⟩ => ⟨⟨
      shift_left (erase_even supp),
      fun n => if Even n then f (n + 1) else 0, by {
        intro a
        simp [Nat.odd_add_one]
        aesop
    }⟩⟩

@[simp]
private lemma oddPart'_coeff {f : Polynomial F} {n : ℕ} :
    (oddPart' f).coeff n = if Even n then f.coeff (n + 1) else 0 := by
  rcases f with ⟨⟨supp, g, h⟩⟩
  simp [oddPart']

private lemma x_times_oddPart'_eq_x_times_oddPart' {f : Polynomial F} :
    Polynomial.X * (oddPart' f) = x_times_oddPart' f := by
  apply Polynomial.ext
  intro n
  rcases n with _ | n <;> try simp [Nat.odd_add_one]

private lemma really_glorious_lemma {f f' : Polynomial F} (h : 2 * f = 2 * f') :
    f = f' := by
    apply Polynomial.ext
    intro n
    have h_2 : (2 * f).coeff n = (2 * f').coeff n := by simp [h]
    simp at h_2
    aesop

private lemma evenPart_eq_evenPart' {f : Polynomial F} : evenPart f = evenPart' f := by
  apply really_glorious_lemma
  rw [evenPart_by_2]
  apply Polynomial.ext
  intro n
  simp [coeffs_of_comp_minus_x]
  by_cases hpar : Even n <;> try simp [hpar]
  ring_nf

private lemma oddPart_eq_oddPart'_aux' {f : Polynomial F}
  : (f - f.comp (-Polynomial.X)) = (Polynomial.C 2) * x_times_oddPart' f := by
  apply Polynomial.ext
  intro n
  simp [coeffs_of_comp_minus_x]
  by_cases hpar : Even n
  · simp [hpar]
  · simp [hpar]
    simp only [← Nat.not_odd_iff_even, Decidable.not_not] at hpar
    simp [hpar]
    ring_nf

private lemma oddPart_eq_oddPart' {f : Polynomial F} : oddPart f = oddPart' f := by
  simp [oddPart]
  rw [oddPart_eq_oddPart'_aux'
  , ←x_times_oddPart'_eq_x_times_oddPart'
  , ←mul_assoc
  , ←Polynomial.C_mul]
  simp [Polynomial.mul_divByMonic_cancel_left]

@[simp]
lemma oddPart_coeff {f : Polynomial F} {n : ℕ} :
    (oddPart f).coeff n = if Even n then f.coeff (n + 1) else 0 := by
  simp [oddPart_eq_oddPart']

@[simp]
lemma evenPart_coeff {f : Polynomial F} {n : ℕ} :
    (evenPart f).coeff n = if Even n then f.coeff n else 0 := by
  simp [evenPart_eq_evenPart']

lemma f_eq_evenPart_plus_x_oddPart {f : Polynomial F} :
  f = evenPart f + Polynomial.X * oddPart f := by
  apply Polynomial.ext
  intro n
  simp
  rw [mul_comm Polynomial.X]
  rcases n with _ | n <;> try simp
  by_cases hPar : Even (n + 1) <;> try simp [hPar]
  · rw [Nat.even_add_one] at hPar
    simp [hPar]
  · rw [Nat.even_add_one] at hPar
    simp at hPar
    simp [hPar]

lemma oddPart_even {f : Polynomial F} :
    EvenPoly (oddPart f) := by
  intro n hOdd
  simp
  intro h
  rw [←Nat.not_even_iff_odd] at hOdd
  tauto

lemma evenPart_even {f : Polynomial F} :
    EvenPoly (evenPart f) := by
  intro n hOdd
  simp
  intro h
  rw [←Nat.not_even_iff_odd] at hOdd
  tauto

lemma evenize_eq_comp_x_squared {f : Polynomial F} :
    evenize f = f.comp (Polynomial.X * Polynomial.X) := by
  apply Polynomial.ext
  intro n
  simp [comp_x_square_coeff]

lemma deevenize_comp_x_squared {f : Polynomial F} (hEven : EvenPoly f) :
    (deevenize f).comp (Polynomial.X * Polynomial.X) = f := by
  apply Polynomial.ext
  intro n
  rw [comp_x_square_coeff]
  simp
  by_cases hPar : Even n <;> simp [hPar]
  · rw [Nat.mul_div_eq_iff_dvd.2 (by {
      rw [Nat.even_iff] at hPar
      omega
    })]
  · symm ; apply hEven
    rw [←Nat.not_even_iff_odd]
    exact hPar

lemma evenize_is_even {f : Polynomial F} :
    EvenPoly (evenize f) := by
  intros n hOdd
  simp
  intros hEven
  rw [←Nat.not_odd_iff_even] at hEven
  tauto

lemma eq_evenize_deevenize {f : Polynomial F} (hEven : EvenPoly f) :
    evenize (deevenize f) = f := by
  apply Polynomial.ext
  intro n
  simp
  by_cases hPar : Even n <;> simp [hPar]
  · rw [Nat.mul_div_eq_iff_dvd.2 (by {
      rw [Nat.even_iff] at hPar
      omega
    })]
  · rw [hEven _ (Nat.not_even_iff_odd.1 hPar)]

lemma even_eval {f : Polynomial F} {s : F} (hEven : EvenPoly f) :
  f.eval (-s) = f.eval s := by
  rw [←eq_evenize_deevenize (f := f) hEven,
      evenize_eq_comp_x_squared]
  simp [Polynomial.eval_comp, Polynomial.eval_mul]

lemma deevenize_evenize {f : Polynomial F} :
    deevenize (evenize f) = f := by
  apply Polynomial.ext
  simp

lemma evenize_eval {f : Polynomial F} {s : F} :
    (evenize f).eval s = f.eval (s * s) := by
  rw [evenize_eq_comp_x_squared]
  simp [Polynomial.eval_comp, Polynomial.eval_mul]

lemma evenPart_x_eval_eq {f : Polynomial F} {s : F} :
    (evenPart_x f).eval (s * s) = (evenPart f).eval s := by
  unfold evenPart_x
  rw [←eq_evenize_deevenize (f := evenPart f)
      , evenize_eval
      , deevenize_evenize]
  exact evenPart_even

lemma oddPart_x_eval_eq {f : Polynomial F} {s : F} :
    (oddPart_x f).eval (s * s) = (oddPart f).eval s := by
  unfold oddPart_x
  rw [←eq_evenize_deevenize (f := oddPart f)
      , evenize_eval
      , deevenize_evenize]
  exact oddPart_even

private lemma x_mul_odd_part_oddpart_eq_odd_part {f : Polynomial F} :
  (X * f.oddPart).oddPart = f.oddPart := by
    apply Polynomial.ext
    intro n
    simp only [oddPart_coeff, coeff_X_mul, ite_eq_left_iff, Nat.not_even_iff_odd, right_eq_ite_iff]
    intro ho he
    rw [←Nat.not_odd_iff_even] at he
    tauto

private lemma deevenize_natDegree_le_natDegree_div_2 {f : Polynomial F} :
  (deevenize f).natDegree ≤ f.natDegree / 2 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [deevenize_coeff]
    rw [Nat.div_lt_iff_lt_mul (by simp)] at hN
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    omega

private lemma natDegree_div_2_le_max_parts_natDegree {f : Polynomial F} :
  f.natDegree / 2 ≤ max f.oddPart.deevenize.natDegree f.evenPart.deevenize.natDegree := by
  conv =>
    lhs
    rw [f_eq_evenPart_plus_x_oddPart (f := f)]
  trans
  apply Nat.div_le_div_right (Polynomial.natDegree_add_le _ _)
  by_cases hodd : f.oddPart = 0
  · simp [hodd]
    conv =>
      lhs
      rw [←deevenize_comp_x_squared (f := f.evenPart) evenPart_even]
    rw [Polynomial.natDegree_comp]
    simp
  · by_cases hle: f.evenPart.natDegree ≤ f.oddPart.natDegree
    · simp only [le_sup_iff]
      rw [mul_comm, Polynomial.natDegree_mul_X (by assumption)]
      rw [max_eq_right (by linarith)]
      rw [Nat.succ_div]
      have h : ¬ 2 ∣ f.oddPart.natDegree + 1 := by
        simp only [Nat.two_dvd_ne_zero]
        rw [←Nat.odd_iff, Nat.odd_add_one, Nat.not_odd_iff_even]
        apply even_poly_has_even_degree
        exact oddPart_even
      simp only [h, ↓reduceIte, add_zero]
      left
      conv =>
        lhs
        rw [←deevenize_comp_x_squared (f := f.oddPart) oddPart_even]
      rw [Polynomial.natDegree_comp]
      simp
    · simp at hle
      rw [max_eq_left (by {
        rw [mul_comm, Polynomial.natDegree_mul_X (by assumption)]
        omega
      })]
      simp only [le_sup_iff]
      right
      conv =>
        lhs
        rw [←deevenize_comp_x_squared (f := f.evenPart) evenPart_even]
      rw [Polynomial.natDegree_comp]
      simp

/-- `foldingPolynomial` representation in terms of
    `evenPart` and `oddPart` when `q = X * X`. -/
@[simp]
lemma even_y_odd_eq_folding_polynomial {f : Polynomial F} :
  FoldingPolynomial.foldingPolynomial (X * X) f 
    = (C (deevenize <| evenPart f)) + X * (C (deevenize <| oddPart f)) 
   := by
  symm
  apply FoldingPolynomial.folding_polynomial_is_unique'
  · simp only [X_mul_C, Polynomial.map_add, map_C, coe_compRingHom, Polynomial.map_mul, map_X,
    eval_add, eval_C, eval_mul, eval_X]
    conv =>
      rhs
      rw [f_eq_evenPart_plus_x_oddPart (f := f)]
    rw [deevenize_comp_x_squared evenPart_even,
        deevenize_comp_x_squared oddPart_even]
    simp [mul_comm]
  · simp only [Bivariate.degreeX, X_mul_C, coeff_add, coeff_C_mul, ne_eq, X_ne_zero,
    not_false_eq_true, natDegree_mul_X, natDegree_X, Nat.reduceAdd]
    simp only [Finset.sup_le_iff, mem_support_iff, coeff_add, coeff_C_mul, ne_eq]
    intro b hb
    rcases b with _ | b
    · simp only [coeff_C_zero, coeff_X_zero, mul_zero, add_zero] at *
      trans
      exact deevenize_natDegree_le_natDegree_div_2
      apply Nat.div_le_div_right
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      simp only [evenPart_coeff, ite_eq_right_iff]
      intro N hN hEven
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hN]
    · rcases b with _ | b <;> try simp [Polynomial.coeff_X]
      simp at *
      trans
      exact deevenize_natDegree_le_natDegree_div_2
      apply Nat.div_le_div_right
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      simp
      intro N hN hEven
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  · simp only [Bivariate.natDegreeY, X_mul_C, natDegree_C_add, ne_eq, X_ne_zero, not_false_eq_true,
    natDegree_mul_X, natDegree_X, Nat.reduceAdd]
    apply Nat.lt_of_le_of_lt Polynomial.natDegree_mul_le
    simp

/-- A representation of FRI `polyFold` function in terms of `evenPart`
    and `oddPart` for the case `k = 2`. -/
@[simp]
lemma poly_fold_k_eq_2 {f : F[X]} {r : F} :
  FoldingPolynomial.polyFold f 2 r 
    = f.evenPart.deevenize + (C r) * f.oddPart.deevenize := by
  simp [FoldingPolynomial.polyFold]
  have h : (X : F[X]) ^ 2 = X * X := by ring
  rw [h]
  simp 
  rw [mul_comm]
  

end Lemmas

end Polynomial

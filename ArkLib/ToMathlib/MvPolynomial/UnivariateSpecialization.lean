/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.BigOperators

/-!
# Univariate specialization and zeros counted along one coordinate

Fix a variable `i` of a multivariate polynomial `p` and an assignment `x` of the variables.
`MvPolynomial.univariateSpecialization p i x` is the univariate polynomial in `X_i` obtained by
evaluating every other variable `X_j` at `x j`; the value `x i` is ignored. Its evaluation at `t` is
`p` evaluated at `Function.update x i t`, its degree is at most `degreeOf i p`, and its derivative
is the specialization of `pderiv i p`.

The counting theorem bounds zeros of `p` in a finite box `∏ j, S j` at which the specialization in
`X_i` is a nonzero polynomial. Fixing the coordinates other than `i` leaves at most `degreeOf i p`
choices for the `i`-th coordinate, so there are at most `degreeOf i p * ∏ j ≠ i, #(S j)` such zeros.
This is a one-variable relative of the Schwartz–Zippel bound: the zeros need not be sparse in
the whole box, but they are sparse along each line parallel to the `i`-th axis on which `p` does
not vanish identically. The main case is a zero at which `pderiv i p` does not vanish, since then
the specialization has nonzero derivative.

The coefficient ring must be a domain: over `ZMod 4`, the polynomial `2 * X` of degree one has the
two zeros `0` and `2`, and its derivative `2` vanishes nowhere.

## Main statements

* `MvPolynomial.univariateSpecialization` with `eval_univariateSpecialization`,
  `univariateSpecialization_update`, `natDegree_univariateSpecialization_le` and
  `derivative_univariateSpecialization`.
* `MvPolynomial.card_le_degreeOf_mul_prod_of_univariateSpecialization_ne_zero`: the count of zeros
  with nonzero specialization.
* `MvPolynomial.card_le_degreeOf_mul_prod_of_eval_pderiv_ne_zero`: the count of zeros at which
  `pderiv i p` does not vanish.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {R σ : Type*}

/-! ### Specialization in one variable -/

/-- Regard `p` as a univariate polynomial in `X_i` and evaluate every other variable `X_j` at
`x j`. The value `x i` is not used. -/
def univariateSpecialization [CommSemiring R] (p : MvPolynomial σ R) (i : σ) (x : σ → R) :
    Polynomial R := by
  classical
  exact Polynomial.map (eval fun j : {j // j ≠ i} ↦ x j) <|
    optionEquivLeft R {j // j ≠ i} <| rename (Equiv.optionSubtypeNe i).symm p

/-- Evaluating the specialization at `t` evaluates `p` at `x` with its `i`-th coordinate replaced
by `t`. -/
theorem eval_univariateSpecialization [CommSemiring R] [DecidableEq σ] (p : MvPolynomial σ R)
    (i : σ) (x : σ → R) (t : R) :
    (p.univariateSpecialization i x).eval t = eval (Function.update x i t) p := by
  rw [univariateSpecialization, ← optionEquivLeft_elim_eval, eval_rename]
  apply congrArg fun assignment ↦ eval assignment p
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [hj]

/-- The specialization does not depend on the `i`-th coordinate of the assignment. -/
@[simp]
theorem univariateSpecialization_update [CommSemiring R] [DecidableEq σ]
    (p : MvPolynomial σ R) (i : σ) (x : σ → R) (t : R) :
    p.univariateSpecialization i (Function.update x i t) = p.univariateSpecialization i x := by
  unfold univariateSpecialization
  congr 2
  funext j
  exact Function.update_of_ne j.2 _ _

/-- Evaluating the other variables does not raise the degree in `X_i`. -/
theorem natDegree_univariateSpecialization_le [CommSemiring R] (p : MvPolynomial σ R) (i : σ)
    (x : σ → R) : (p.univariateSpecialization i x).natDegree ≤ p.degreeOf i := by
  classical
  rw [univariateSpecialization, degreeOf_eq_natDegree]
  exact Polynomial.natDegree_map_le

/-- Under `optionEquivLeft`, the partial derivative in the variable `none` is the ordinary
derivative. -/
theorem derivative_optionEquivLeft [CommSemiring R] (p : MvPolynomial (Option σ) R) :
    Polynomial.derivative (optionEquivLeft R σ p) = optionEquivLeft R σ (pderiv none p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      cases j with
      | none => simp [hp, Polynomial.derivative_mul, mul_comm]
      | some j => simp [hp, Polynomial.derivative_mul, mul_comm]

/-- Specializing the other variables commutes with differentiation in `X_i`. -/
theorem derivative_univariateSpecialization [CommSemiring R] (p : MvPolynomial σ R) (i : σ)
    (x : σ → R) :
    Polynomial.derivative (p.univariateSpecialization i x) =
      (pderiv i p).univariateSpecialization i x := by
  classical
  rw [univariateSpecialization, univariateSpecialization, Polynomial.derivative_map,
    derivative_optionEquivLeft]
  congr 2
  simpa using pderiv_rename (Equiv.optionSubtypeNe i).symm.injective i p

/-- If `pderiv i p` does not vanish at `x`, then the specialization of `p` in `X_i` at `x` is a
nonzero polynomial, because its derivative does not vanish at `x i`. -/
theorem univariateSpecialization_ne_zero_of_eval_pderiv_ne_zero [CommSemiring R]
    {p : MvPolynomial σ R} {i : σ} {x : σ → R} (hx : eval x (pderiv i p) ≠ 0) :
    p.univariateSpecialization i x ≠ 0 := by
  classical
  intro hzero
  apply hx
  have h := congrArg (fun q ↦ (Polynomial.derivative q).eval (x i)) hzero
  simpa [derivative_univariateSpecialization, eval_univariateSpecialization] using h

/-! ### Counting zeros along one coordinate -/

/-- **Zeros counted along one coordinate.** Let `T` be a finite set of points of the box
`∏ j, S j` at which `p` vanishes and the specialization of `p` in `X_i` is a nonzero polynomial.
Then `#T ≤ degreeOf i p * ∏ j ≠ i, #(S j)`.

Points of `T` with the same coordinates away from `i` share one nonzero specialization, of degree
at most `degreeOf i p`, and their `i`-th coordinates are roots of it. The domain hypothesis is what
bounds the number of roots by the degree; the statement fails over `ZMod 4` for `p = 2 * X`. The
nonzero-specialization hypothesis cannot be dropped: every point is a zero of `p = 0`. When
`S i` is empty, the box is empty and the bound holds trivially. -/
theorem card_le_degreeOf_mul_prod_of_univariateSpecialization_ne_zero [CommRing R] [IsDomain R]
    [Fintype σ] [DecidableEq σ] (S : σ → Finset R) (i : σ) (p : MvPolynomial σ R)
    (T : Finset (σ → R))
    (hT : ∀ x ∈ T, x ∈ Fintype.piFinset S ∧ eval x p = 0 ∧ p.univariateSpecialization i x ≠ 0) :
    T.card ≤ p.degreeOf i * ∏ j ∈ Finset.univ.erase i, (S j).card := by
  classical
  rcases (S i).eq_empty_or_nonempty with hS | ⟨c, hc⟩
  · have hT' : T = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_
      have hxi := Fintype.mem_piFinset.mp (hT x hx).1 i
      simp [hS] at hxi
    simp [hT']
  rw [← Fintype.card_filter_piFinset_eq_of_mem S i hc]
  refine Finset.card_le_mul_card_image_of_maps_to (f := fun x ↦ Function.update x i c)
    (fun x hx ↦ ?_) _ fun y _ ↦ ?_
  · refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j ↦ ?_, by simp⟩
    by_cases hj : j = i
    · subst j
      simpa using hc
    · simpa [Function.update_of_ne hj] using Fintype.mem_piFinset.mp (hT x hx).1 j
  set fibre := T.filter fun x ↦ Function.update x i c = y
  rcases fibre.eq_empty_or_nonempty with hfibre | ⟨x₀, hx₀⟩
  · simp [hfibre]
  have hspec : ∀ x ∈ fibre,
      p.univariateSpecialization i x = p.univariateSpecialization i y := by
    intro x hx
    rw [← (Finset.mem_filter.mp hx).2, univariateSpecialization_update]
  have hne : p.univariateSpecialization i y ≠ 0 := by
    rw [← hspec x₀ hx₀]
    exact (hT x₀ (Finset.mem_filter.mp hx₀).1).2.2
  have hrecover : ∀ x ∈ fibre, x = Function.update y i (x i) := by
    intro x hx
    rw [← (Finset.mem_filter.mp hx).2, Function.update_idem, Function.update_eq_self]
  calc
    fibre.card ≤ (p.univariateSpecialization i y).roots.toFinset.card := by
      refine Finset.card_le_card_of_injOn (fun x ↦ x i) (fun x hx ↦ ?_) fun x hx x' hx' hxx' ↦ ?_
      · rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
          ← hspec x hx, eval_univariateSpecialization, Function.update_eq_self]
        exact (hT x (Finset.mem_filter.mp hx).1).2.1
      · rw [hrecover x hx, hrecover x' hx']
        simp only at hxx'
        rw [hxx']
    _ ≤ Multiset.card (p.univariateSpecialization i y).roots := Multiset.toFinset_card_le _
    _ ≤ (p.univariateSpecialization i y).natDegree := Polynomial.card_roots' _
    _ ≤ p.degreeOf i := natDegree_univariateSpecialization_le p i y

/-- **Zeros with nonvanishing partial derivative.** A finite set of points of the box
`∏ j, S j` at which `p` vanishes and `pderiv i p` does not has at most
`degreeOf i p * ∏ j ≠ i, #(S j)` elements.

This is `card_le_degreeOf_mul_prod_of_univariateSpecialization_ne_zero`, since a nonzero partial
derivative at `x` makes the specialization in `X_i` nonzero. -/
theorem card_le_degreeOf_mul_prod_of_eval_pderiv_ne_zero [CommRing R] [IsDomain R]
    [Fintype σ] [DecidableEq σ] (S : σ → Finset R) (i : σ) (p : MvPolynomial σ R)
    (T : Finset (σ → R))
    (hT : ∀ x ∈ T, x ∈ Fintype.piFinset S ∧ eval x p = 0 ∧ eval x (pderiv i p) ≠ 0) :
    T.card ≤ p.degreeOf i * ∏ j ∈ Finset.univ.erase i, (S j).card :=
  card_le_degreeOf_mul_prod_of_univariateSpecialization_ne_zero S i p T fun x hx ↦
    ⟨(hT x hx).1, (hT x hx).2.1,
      univariateSpecialization_ne_zero_of_eval_pderiv_ne_zero (hT x hx).2.2⟩

end

end MvPolynomial
